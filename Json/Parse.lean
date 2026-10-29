/-
  The JSON parser. It reads a list of characters and returns a value
  and the characters that follow it, or `none` when the text up to
  that point sits outside the grammar of RFC 8259.

  Rules the parser follows:

  - Whitespace is space, tab, line feed, and carriage return, and
    nothing else. It may sit before a value, after a value, and
    around the marks inside an array or an object.
  - A control character inside a string must be escaped. The escapes
    are the ones RFC 8259 lists, plus `\uXXXX`.
  - A `\uXXXX` escape in the high surrogate range must be followed
    by a second `\uXXXX` escape in the low surrogate range, and the
    pair is read as one character. A lone surrogate escape is
    rejected, because Lean `Char` cannot hold a surrogate half.
  - A number is read by the grammar of RFC 8259 and held as its
    source text.

  `parseValue`, `parseEls`, and `parseObjEls` take a fuel count.
  Each step into an array or an object spends one unit, so the
  functions are total on hostile input: a text that nests deeper
  than its own length is rejected, never looped on. The top level
  `parse` passes one more than the length of the text, which is
  always enough for a text the grammar accepts.
-/

import Json.Value

namespace Json

/-- Whitespace in JSON: space, tab, line feed, carriage return. -/
def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Drop the whitespace at the head of the text. -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

/-- A digit, as a test. -/
def isDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9')

/-- The value of one hex digit, in either case. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- The character a one letter escape stands for. -/
def simpleEscape (c : Char) : Option Char :=
  if c = '"' then some '"'
  else if c = '\\' then some '\\'
  else if c = '/' then some '/'
  else if c = 'b' then some (Char.ofNat 8)
  else if c = 'f' then some (Char.ofNat 12)
  else if c = 'n' then some (Char.ofNat 10)
  else if c = 'r' then some (Char.ofNat 13)
  else if c = 't' then some (Char.ofNat 9)
  else none

/-- Read a string body, up to the closing quote. The opening quote is
    already consumed. Returns the characters read and the text after
    the closing quote. -/
def parseStrBody : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '"' then some ([], rest)
    else if c = '\\' then
      match rest with
      | [] => none
      | e :: rest1 =>
        if e = 'u' then
          match rest1 with
          | a :: b :: cc :: d :: rest2 =>
            match hexVal a, hexVal b, hexVal cc, hexVal d with
            | some w, some x, some y, some z =>
              let n := w * 4096 + x * 256 + y * 16 + z
              if n < 0xD800 then
                (parseStrBody rest2).map fun (cs, r) => (Char.ofNat n :: cs, r)
              else if n < 0xDC00 then
                match rest2 with
                | '\\' :: 'u' :: a2 :: b2 :: c2 :: d2 :: rest3 =>
                  match hexVal a2, hexVal b2, hexVal c2, hexVal d2 with
                  | some w2, some x2, some y2, some z2 =>
                    let m := w2 * 4096 + x2 * 256 + y2 * 16 + z2
                    if 0xDC00 ≤ m ∧ m < 0xE000 then
                      (parseStrBody rest3).map fun (cs, r) =>
                        (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)) :: cs, r)
                    else none
                  | _, _, _, _ => none
                | _ => none
              else if n < 0xE000 then none
              else
                (parseStrBody rest2).map fun (cs, r) => (Char.ofNat n :: cs, r)
            | _, _, _, _ => none
          | _ => none
        else
          match simpleEscape e with
          | some ch => (parseStrBody rest1).map fun (cs, r) => (ch :: cs, r)
          | none => none
    else if c.toNat < 0x20 then none
    else (parseStrBody rest).map fun (cs, r) => (c :: cs, r)

/-- The longest run of digits at the head of the text, and the text
    after it. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isDigit c then
      let (ds, r) := takeDigits rest
      (c :: ds, r)
    else ([], c :: rest)

/-- The integer part of a number: a single zero, or a non-zero digit
    and the digits after it. -/
def parseIntPart (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | [] => none
  | c :: rest =>
    if c = '0' then some (['0'], rest)
    else if '1' ≤ c ∧ c ≤ '9' then
      let (ds, r) := takeDigits rest
      some (c :: ds, r)
    else none

/-- The fraction part of a number when one is there: a point and one
    or more digits. When the next character is not a point, the part
    is empty. -/
def parseFracOpt (cs : List Char) : Option (List Char × List Char) :=
  if cs.head? = some '.' then
    match takeDigits cs.tail with
    | (d :: ds, r) => some ('.' :: d :: ds, r)
    | _ => none
  else some ([], cs)

/-- The exponent part of a number when one is there: `e` or `E`, an
    optional sign, and one or more digits. When the next character is
    not one of the two letters, the part is empty. -/
def parseExpOpt (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | e :: rest =>
    if e = 'e' ∨ e = 'E' then
      let (sgn, rest1) : List Char × List Char :=
        if rest.head? = some '+' then (['+'], rest.tail)
        else if rest.head? = some '-' then (['-'], rest.tail)
        else ([], rest)
      match takeDigits rest1 with
      | (d :: ds, r) => some (e :: (sgn ++ d :: ds), r)
      | _ => none
    else some ([], cs)
  | [] => some ([], [])

/-- Read a number at the head of the text. Returns the number text
    and the text after it. The grammar is the one in RFC 8259: an
    optional minus, an integer part, a fraction part, an exponent
    part. -/
def parseNumber (cs : List Char) : Option (List Char × List Char) :=
  let (sgn, rest) : List Char × List Char :=
    if cs.head? = some '-' then (['-'], cs.tail) else ([], cs)
  match parseIntPart rest with
  | none => none
  | some (i, r1) =>
    match parseFracOpt r1 with
    | none => none
    | some (f, r2) =>
      match parseExpOpt r2 with
      | none => none
      | some (e, r3) => some (sgn ++ i ++ f ++ e, r3)

mutual
/-- Read one value at the head of the text, after any whitespace.
    The fuel count bounds how deep arrays and objects may nest. -/
def parseValue : Nat → List Char → Option (Json × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | [] => none
    | c :: rest =>
      if c = '"' then
        (parseStrBody rest).map fun (s, r) => (Json.str s, r)
      else if c = '[' then
        (parseEls fuel rest).map fun (vs, r) => (Json.arr vs, r)
      else if c = '{' then
        (parseObjEls fuel rest).map fun (kvs, r) => (Json.obj kvs, r)
      else if c = 't' then
        match rest with
        | 'r' :: 'u' :: 'e' :: r => some (Json.bool true, r)
        | _ => none
      else if c = 'f' then
        match rest with
        | 'a' :: 'l' :: 's' :: 'e' :: r => some (Json.bool false, r)
        | _ => none
      else if c = 'n' then
        match rest with
        | 'u' :: 'l' :: 'l' :: r => some (Json.null, r)
        | _ => none
      else if c = '-' ∨ isDigit c then
        (parseNumber (c :: rest)).map fun (n, r) => (Json.num n, r)
      else none

/-- Read the inside of an array, after the opening bracket: values
    split by commas, then the closing bracket. -/
def parseEls : Nat → List Char → Option (List Json × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | [] => none
    | c :: rest =>
      if c = ']' then some ([], rest)
      else
        match parseValue fuel (c :: rest) with
        | none => none
        | some (v, r) =>
          match skipWs r with
          | ']' :: r2 => some ([v], r2)
          | ',' :: r2 =>
            match skipWs r2 with
            | ']' :: _ => none
            | [] => none
            | _ =>
              (parseEls fuel r2).map fun (vs, r3) => (v :: vs, r3)
          | _ => none

/-- Read the inside of an object, after the opening brace: key and
    value pairs split by commas, then the closing brace. -/
def parseObjEls : Nat → List Char → Option (List (List Char × Json) × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | [] => none
    | c :: rest =>
      if c = '}' then some ([], rest)
      else if c = '"' then
        match parseStrBody rest with
        | none => none
        | some (k, r1) =>
          match skipWs r1 with
          | ':' :: r2 =>
            match parseValue fuel r2 with
            | none => none
            | some (v, r3) =>
              match skipWs r3 with
              | '}' :: r4 => some ([(k, v)], r4)
              | ',' :: r4 =>
                match skipWs r4 with
                | '"' :: _ =>
                  (parseObjEls fuel r4).map fun (kvs, r5) => ((k, v) :: kvs, r5)
                | _ => none
              | _ => none
          | _ => none
      else none
end

/-- Parse a whole text: one value, with whitespace allowed around it
    and nothing after it. -/
def parse (cs : List Char) : Option Json :=
  match parseValue (cs.length + 1) cs with
  | some (v, rest) => if skipWs rest = [] then some v else none
  | none => none

end Json

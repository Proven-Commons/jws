/-
  The JSON value type, the canonical printer, and the well formed
  predicate that the round trip proof in `Proofs` uses.

  A number is held as its source text. The printer writes that text
  back word for word, and no claim is made about the numeric value.
  The parser in `Json.Parse` checks the text against the number
  grammar of RFC 8259 before it builds a `num` value.

  A string is held as a list of characters. Lean `Char` is a Unicode
  scalar value, so a string here can never hold a lone surrogate half.

  An object is held as a list of key and value pairs, in the order
  written. Duplicate keys are kept as written.
-/

namespace Json

/-- A JSON value. Numbers and strings and object keys are held as
    lists of characters. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (cs : List Char)
  | str (cs : List Char)
  | arr (vs : List Json)
  | obj (kvs : List (List Char × Json))

/-- The sixteen hex digits, lowercase. -/
def hexDigits : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- The hex digit for a value below 16. -/
def hexDigit (n : Nat) : Char :=
  hexDigits.getD n '0'

/-- The printed form of one character inside a string. The quote and
    the backslash take a backslash before them. The five control
    characters that have a short form in RFC 8259 use it. Any other
    character below U+0020 is written as `\u00XX`. Every other
    character is written as it is. -/
def escape (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat = 8 then ['\\', 'b']
  else if c.toNat = 9 then ['\\', 't']
  else if c.toNat = 10 then ['\\', 'n']
  else if c.toNat = 12 then ['\\', 'f']
  else if c.toNat = 13 then ['\\', 'r']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

/-- The printed form of a whole string body, without the quotes. -/
def escapeAll (cs : List Char) : List Char :=
  cs.flatMap escape

/-- A string in its printed form, with quotes. -/
def printStr (cs : List Char) : List Char :=
  '"' :: (escapeAll cs ++ ['"'])

/-- Join printed parts with a comma between each two. -/
def join : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: y :: rest => x ++ ',' :: join (y :: rest)

mutual
/-- The canonical printed form of a value: no spaces anywhere,
    object pairs in the order held, numbers as their source text. -/
def print : Json → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .num cs => cs
  | .str cs => printStr cs
  | .arr vs => '[' :: join (vs.map print) ++ [']']
  | .obj kvs => '{' :: join (kvs.map printPair) ++ ['}']

/-- One object pair in its printed form. -/
def printPair : List Char × Json → List Char
  | (k, v) => printStr k ++ ':' :: print v
end

/-- A digit, as a proposition. -/
def IsDigit (c : Char) : Prop :=
  '0' ≤ c ∧ c ≤ '9'

/-- The fraction part of a number text, as RFC 8259 allows it: either
    absent, or a point and one or more digits. -/
def FracOk (f : List Char) : Prop :=
  f = [] ∨ ∃ d ds, f = '.' :: d :: ds ∧ IsDigit d ∧ ∀ x ∈ ds, IsDigit x

/-- The exponent part of a number text: either absent, or `e` or `E`,
    an optional sign, and one or more digits. -/
def ExpOk (e : List Char) : Prop :=
  e = [] ∨ ∃ (ec : Char) (sgn : List Char) (d : Char) (ds : List Char),
    e = ec :: (sgn ++ d :: ds) ∧ (ec = 'e' ∨ ec = 'E') ∧
    (sgn = [] ∨ sgn = ['-'] ∨ sgn = ['+']) ∧
    IsDigit d ∧ ∀ x ∈ ds, IsDigit x

/-- A number text that follows the grammar of RFC 8259: an optional
    minus, then either a single zero or a non-zero digit and more
    digits, then a fraction part and an exponent part. Stated as a
    split of the text into its parts. -/
def WFNum (cs : List Char) : Prop :=
  ∃ (neg : Bool) (hd : Char) (intDs frac exp : List Char),
    cs = (if neg then ['-'] else []) ++ (hd :: intDs) ++ frac ++ exp ∧
    ((hd = '0' ∧ intDs = []) ∨ ('1' ≤ hd ∧ hd ≤ '9')) ∧
    (∀ d ∈ intDs, IsDigit d) ∧ FracOk frac ∧ ExpOk exp

/-- A value whose number texts all follow the grammar. Strings,
    object keys, and the shape of arrays and objects need no further
    condition: every such value prints in a form the parser reads
    back. -/
inductive WF : Json → Prop
  | null : WF .null
  | bool (b : Bool) : WF (.bool b)
  | num {cs : List Char} : WFNum cs → WF (.num cs)
  | str (cs : List Char) : WF (.str cs)
  | arr {vs : List Json} : (∀ v ∈ vs, WF v) → WF (.arr vs)
  | obj {kvs : List (List Char × Json)} : (∀ kv ∈ kvs, WF kv.2) → WF (.obj kvs)

end Json

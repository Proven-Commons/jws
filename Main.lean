import Jws

/-
  Command line front end. The shape follows the other slices in
  this org: one request per line on stdin, one answer per line
  on stdout. A request is a word, a space, and a payload. The
  payload is decimal character codes separated by commas.

  One operation:

    check  the payload carries six fields separated by
           semicolons (code 59). Each field is text written as
           character codes, as above. Field 1: the token text.
           Field 2: the current time as decimal digits, or empty
           for no time comparisons. Field 3: the allowed
           algorithms, names separated by commas inside the
           field text. Field 4: the required claims, same style.
           A name in field 3 or 4 is never empty: a leading,
           trailing or doubled comma makes the request malformed.
           Field 5: the expected issuer, or empty. Field 6: the
           expected audience, or empty.

  The answer is `ok:` and the codes of the token text as
  received when the token is accepted (`Jws.printToken` of the
  parsed token, which `Jws.Spec.printToken_parse` proves is the
  received text, so its signing input still matches its
  signature), `none` when it is not, and `error` when the request
  itself is malformed.

  Full statement of the format and the rules: SPEC.md.
-/

/-- One decimal number, at most seven digits, the way the house
    writes a character code. -/
def number (s : String) : Option Nat :=
  if s.isEmpty ∨ ¬ s.all (·.isDigit) then none
  else
    let n := s.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
    if n < 10000000 then some n else none

/-- The comma separated numbers of a payload or a field. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn ",").mapM number

/-- Numbers into characters, asking each number to be a scalar
    value: below the surrogate gap or above it, within range. -/
def toChars (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n =>
    if n < 0xD800 ∨ (0xE000 ≤ n ∧ n ≤ 0x10FFFF) then some (Char.ofNat n)
    else none

/-- Characters back into the comma separated answer codes. -/
def showCodes (cs : List Char) : String :=
  ",".intercalate (cs.map fun c => toString c.toNat)

/-- Remove one trailing newline and carriage return. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

/-- Split a field text into names at its commas. An empty field
    names nothing. A name may not be empty, so a field with a
    leading, trailing or doubled comma is malformed (`none`): the
    text `HS256,` would otherwise put the empty name on the
    allowlist, and a header whose `alg` is the empty string would
    pass. -/
def names (cs : List Char) : Option (List (List Char)) :=
  if cs.isEmpty then some []
  else
    let ns := Jws.splitSep ',' cs
    if ns.any (·.isEmpty) then none else some ns

/-- Read the current time field: empty for no time comparisons,
    else an optional minus sign and at most 19 digits. -/
def readNow (cs : List Char) : Option (Option Int) :=
  match cs with
  | [] => some none
  | _ =>
    let (neg, ds) := match cs with
      | '-' :: r => (true, r)
      | _ => (false, cs)
    if ds.isEmpty ∨ ds.length > 19 ∨ ¬ ds.all (·.isDigit) then none
    else
      let n : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      some (some (if neg then -(n : Int) else (n : Int)))

/-- Answer one `check` request: the codes of the six fields. -/
def answerCheck (fields : List (List Nat)) : Option String :=
  match fields with
  | [tf, nf, af, rf, isf, auf] =>
    match toChars tf, toChars nf, toChars af, toChars rf, toChars isf, toChars auf with
    | some t, some nowCs, some allowCs, some reqCs, some issCs, some audCs =>
      match readNow nowCs, names allowCs, names reqCs with
      | some now, some allow, some required =>
        let ctx : Jws.Context :=
          { allow := allow
            now := now
            required := required
            issuer := if issCs.isEmpty then none else some issCs
            audience := if audCs.isEmpty then none else some audCs }
        match Jws.parseToken t with
        | none => some "none"
        | some tok =>
          some (if Jws.accept tok ctx then "ok:" ++ showCodes (Jws.printToken tok)
                else "none")
      | _, _, _ => none
    | _, _, _, _, _, _ => none
  | _ => none

/-- Answer one request line. -/
def answer (line : String) : String :=
  let line := chomp line
  if line.isEmpty then "error"
  else
    match line.splitOn " " with
    | [op, arg] =>
      if op = "check" then
        match (arg.splitOn ";").mapM numbers with
        | some fields =>
          match answerCheck fields with
          | some out => out
          | none => "error"
        | none => "error"
      else "error"
    | _ => "error"

partial def loop : IO Unit := do
  let stdin ← IO.getStdin
  match ← stdin.getLine with
  | "" => return
  | line =>
    IO.println (answer line)
    loop

def main : IO Unit := loop

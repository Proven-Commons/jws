/-
  The definitions the statements in `Jws/Spec.lean` use besides the code
  under proof. They give the decimal value of a JSON number text,
  written from RFC 8259 section 6 (the number grammar) and plain
  positional notation, separately from the checker's own reading
  (`Jws.numVal` and `Jws.NumVal.cmp` in `Jws/Token.lean`). The
  statements in `Jws/Spec.lean` tie the checker's reading to these.

  This file is part of the specification: a reviewer approves it
  with `Jws/Spec.lean` and `SPEC.md`. It imports nothing from the
  project.
-/

namespace Jws.Spec

/-- The value of a run of decimal digit characters, most significant
    first: each digit times ten to the count of digits after it. -/
def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + digitsValue cs

/-- The power of ten a JSON exponent part denotes (RFC 8259 section
    6). The part is the letter `e` or `E`, then `-`, `+` or no sign,
    then digits; it denotes the digits' value, negated after `-`. No
    exponent part denotes zero. -/
def expValue : List Char → Int
  | [] => 0
  | _ :: '-' :: ds => -(digitsValue ds : Int)
  | _ :: '+' :: ds => (digitsValue ds : Int)
  | _ :: ds => (digitsValue ds : Int)

/-- The text of a JSON number from its pieces (RFC 8259 section 6):
    a minus sign when `neg`, the integer digits, then a point and
    the fraction digits when there are any, then the exponent part
    as written. -/
def numberText (neg : Bool) (ints frac ex : List Char) : List Char :=
  (if neg then ['-'] else []) ++ ints ++ (if frac = [] then [] else '.' :: frac) ++ ex

/-- The decimal `(-1 if neg) * sig * 10^exp`, written as a whole
    number over the power of ten `10^m`. For any `m` at most `exp`
    this is exactly the decimal times `10^(-m)`, so two decimals
    compare as these whole numbers compare over one `m` at most
    both exponents. -/
def atBase (neg : Bool) (sig : Nat) (exp m : Int) : Int :=
  (if neg then -1 else 1) * ((sig * 10 ^ (exp - m).toNat : Nat) : Int)

end Jws.Spec

import Json
import Jws.Base64url
import Jws.Utf8

/-
  The JWS compact form (RFC 7515 section 5.2): three base64url
  parts joined by dots. Part one is the header, a JSON object.
  Part two is the payload, the claims set, also a JSON object.
  Part three is the signature bytes.

  This slice parses the compact form and runs the plan's checks:
  the algorithm against a caller allowlist, the required claims,
  and the exp, nbf, iss, and aud claims against a context the
  caller supplies. It does not verify the signature; a token that
  passes these checks is not thereby verified. Signature
  verification belongs to the second slice.

  The JSON code is the json repo's, carried in unchanged (the
  repos in this org do not import each other): `Json.parse` reads
  a text, `Json.print` writes a value in the canonical form, and
  the round trip between them is proved there for well formed
  values.
-/

namespace Jws

open Json

/-- Split a text at every copy of a separator character. The
    parts never contain the separator. Splitting also serves the
    comma separated name lists of the command line front end. -/
def splitSep (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    if c = sep then [] :: splitSep sep rest
    else
      match splitSep sep rest with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- Join parts with a separator character between them. -/
def joinSep (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ sep :: joinSep sep (q :: ps)

/-- A parsed token: the header value, the claims value, and the
    signature bytes, returned unchanged. -/
structure Token where
  header : Json
  claims : Json
  sig : List UInt8

/-- Print a token: each JSON part in the canonical printer's
    form, UTF-8 bytes, base64url without padding, the parts
    joined by dots, the signature last. -/
def printToken (t : Token) : List Char :=
  joinSep '.' [Base64url.encode (Utf8.encode (Json.print t.header)),
    Base64url.encode (Utf8.encode (Json.print t.claims)),
    Base64url.encode t.sig]

/-- Parse the compact form. Framing first: exactly three parts.
    Each part must decode as strict base64url, the first two must
    then decode as UTF-8 and parse as JSON. Object shape and the
    claim rules are the checker's work, not the parser's. -/
def parseToken (cs : List Char) : Option Token :=
  match splitSep '.' cs with
  | [h, p, s] =>
    match Base64url.decode h, Base64url.decode p, Base64url.decode s with
    | some hb, some pb, some sb =>
      match Utf8.decode hb, Utf8.decode pb with
      | some hc, some pc =>
        match Json.parse hc, Json.parse pc with
        | some hv, some pv => some ⟨hv, pv, sb⟩
        | _, _ => none
      | _, _ => none
    | _, _, _ => none
  | _ => none

/-- An exact decimal number value, read from a JSON number text:
    the value is (if neg then -1 else 1) times sig times ten to
    the exp. The form is normalized: zero is (false, 0, 0), and
    any other sig does not end in zero. -/
structure NumVal where
  neg : Bool
  sig : Nat
  exp : Int
deriving DecidableEq

/-- The value of a run of digit characters. -/
def digitsVal (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- Divide factors of ten out of a significand, raising the
    exponent to match. The fuel is the significand itself, which
    is always more steps than stripping can take. -/
def strip (neg : Bool) : Nat → Nat → Int → NumVal
  | 0, s, e => ⟨neg, s, e⟩
  | fuel + 1, s, e =>
    if s % 10 = 0 ∧ s ≠ 0 then strip neg fuel (s / 10) (e + 1)
    else ⟨neg, s, e⟩

/-- Build a normalized number value. -/
def mkNumVal (neg : Bool) (sig : Nat) (exp : Int) : NumVal :=
  if sig = 0 then ⟨false, 0, 0⟩ else strip neg sig sig exp

/-- Read a JSON number text as an exact decimal value. The text
    is one the JSON parser accepted, so its shape is the number
    grammar; anything else is turned away by returning none. -/
def numVal (cs : List Char) : Option NumVal :=
  let (neg, r0) := match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (ids, r1) := r0.span (·.isDigit)
  if ids.isEmpty then none
  else
    match r1 with
    | '.' :: r =>
      let (fds, r2) := r.span (·.isDigit)
      if fds.isEmpty then none
      else finish neg ids fds r2
    | _ => finish neg ids [] r1
where
  finish (neg : Bool) (ids fds : List Char) (r : List Char) : Option NumVal :=
    match r with
    | [] => some (mkNumVal neg (digitsVal (ids ++ fds)) (-(fds.length : Int)))
    | 'e' :: t => withExp neg ids fds t
    | 'E' :: t => withExp neg ids fds t
    | _ => none
  withExp (neg : Bool) (ids fds : List Char) (r : List Char) : Option NumVal :=
    let (sgn, r1) := match r with
      | '-' :: t => ((-1 : Int), t)
      | '+' :: t => ((1 : Int), t)
      | _ => ((1 : Int), r)
    let (eds, r2) := r1.span (·.isDigit)
    if eds.isEmpty ∨ ¬ r2.isEmpty then none
    else
      some (mkNumVal neg (digitsVal (ids ++ fds))
        (sgn * (digitsVal eds : Int) - (fds.length : Int)))

/-- Whether a number value is a whole number of seconds. -/
def NumVal.isInt (v : NumVal) : Bool :=
  v.sig = 0 || 0 ≤ v.exp

/-- A whole number as a number value. -/
def NumVal.ofInt (n : Int) : NumVal :=
  mkNumVal (n < 0) n.natAbs 0

/-- The count of digits a number is written with. -/
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)
termination_by n
decreasing_by omega

/-- Compare the magnitudes of two nonzero number values. The
    decimal point position decides first. On a tie the
    significands are aligned by padding the shorter one with
    zeros, and the padding counts are digit counts, so a wild
    exponent never turns into a wild power of ten. -/
def magCmp (a b : NumVal) : Ordering :=
  let da := (numDigits a.sig : Int) + a.exp
  let db := (numDigits b.sig : Int) + b.exp
  if da < db then .lt
  else if da > db then .gt
  else
    let dsa := numDigits a.sig
    let dsb := numDigits b.sig
    if dsb ≤ dsa then compare a.sig (b.sig * 10 ^ (dsa - dsb))
    else compare (a.sig * 10 ^ (dsb - dsa)) b.sig

/-- Compare two number values exactly. -/
def NumVal.cmp (a b : NumVal) : Ordering :=
  let sa : Int := if a.sig = 0 then 0 else if a.neg then -1 else 1
  let sb : Int := if b.sig = 0 then 0 else if b.neg then -1 else 1
  if sa < sb then .lt
  else if sa > sb then .gt
  else if sa = 0 then .eq
  else if sa = 1 then magCmp a b
  else magCmp b a

/-- Look a name up in the members of a JSON object. When a name
    appears more than once, the first copy is the one found, as
    in the JSON code. Anything that is not an object has no
    members. -/
def lookup (name : List Char) (j : Json) : Option Json :=
  match j with
  | .obj kvs => kvs.lookup name
  | _ => none

/-- The state of one date claim (exp, nbf, iat) in a claims set:
    absent, present but not a whole number of seconds (a
    non-number, or a number with a fraction), or present with a
    whole number value. -/
inductive ClaimDate where
  | absent
  | bad
  | ok (v : NumVal)

def dateClaim (name : List Char) (claims : Json) : ClaimDate :=
  match lookup name claims with
  | none => .absent
  | some (.num cs) =>
    match numVal cs with
    | some v => if v.isInt then .ok v else .bad
    | none => .bad
  | some _ => .bad

/-- The check context a caller supplies: the algorithms allowed,
    the current time in seconds (none means the time comparisons
    are skipped; the type rules still hold), the claims that must
    be present, the expected issuer if any, the expected audience
    if any. -/
structure Context where
  allow : List (List Char)
  now : Option Int
  required : List (List Char)
  issuer : Option (List Char)
  audience : Option (List Char)

/-- When iss is present it must be a string. -/
def issShapeOk (claims : Json) : Bool :=
  match lookup "iss".toList claims with
  | none => true
  | some (.str _) => true
  | some _ => false

/-- When aud is present it must be a string or an array of
    strings. -/
def audShapeOk (claims : Json) : Bool :=
  match lookup "aud".toList claims with
  | none => true
  | some (.str _) => true
  | some (.arr vs) => vs.all fun v => match v with
    | .str _ => true
    | _ => false
  | some _ => false

/-- The audience check itself: aud is the expected string, or an
    array holding it. A missing aud fails. -/
def audOk (claims : Json) (a : List Char) : Bool :=
  match lookup "aud".toList claims with
  | some (.str s) => s == a
  | some (.arr vs) => vs.any fun v => match v with
    | .str s => s == a
    | _ => false
  | _ => false

/-- Run the checks. Every rule must hold; SPEC.md states them one
    by one. This checks the token's shape and claims only. It
    does not verify the signature, and a true answer here is not
    a verified token. -/
def accept (t : Token) (ctx : Context) : Bool :=
  if ctx.allow.contains "none".toList then false
  else
    match t.header, t.claims with
    | .obj _, .obj _ =>
      match lookup "alg".toList t.header with
      | some (.str alg) =>
        alg != "none".toList &&
        ctx.allow.contains alg &&
        ctx.required.all (fun n => (lookup n t.claims).isSome) &&
        (match dateClaim "exp".toList t.claims with
         | .bad => false
         | .absent => true
         | .ok v => match ctx.now with
           | none => true
           | some n => NumVal.cmp (NumVal.ofInt n) v == .lt) &&
        (match dateClaim "nbf".toList t.claims with
         | .bad => false
         | .absent => true
         | .ok v => match ctx.now with
           | none => true
           | some n => NumVal.cmp (NumVal.ofInt n) v != .lt) &&
        (match dateClaim "iat".toList t.claims with
         | .bad => false
         | _ => true) &&
        issShapeOk t.claims &&
        audShapeOk t.claims &&
        (match ctx.issuer with
         | none => true
         | some i => match lookup "iss".toList t.claims with
           | some (.str s) => s == i
           | _ => false) &&
        (match ctx.audience with
         | none => true
         | some a => audOk t.claims a)
      | _ => false
    | _, _ => false

end Jws

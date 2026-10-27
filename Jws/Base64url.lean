/-
  Base64url, as RFC 4648 section 5 defines it and RFC 7515 uses it:
  the URL and filename safe alphabet, with no padding.

  The shape follows the Base64 code in the codec repo: three bytes
  at a time into four characters on the way out, four characters at
  a time into three bytes on the way back. The differences are the
  last two alphabet characters (`-` and `_`) and the missing
  padding: a final byte is carried by two characters, two final
  bytes by three, and no `=` is ever written or read.

  `decode` is strict. It turns away: any character outside the
  alphabet (`=` among them, since padding is not part of the
  compact form), a length that is 1 mod 4, and a last character
  whose unused bits are not zero.
-/

namespace Jws.Base64url

/-- The character for a value below 64: the alphabet in order,
    capitals (values 0 to 25), small letters (26 to 51), digits
    (52 to 61), then `-` (62) and `_` (63). -/
def char (n : Nat) : Char :=
  if n < 26 then Char.ofNat (n + 65)
  else if n < 52 then Char.ofNat (n + 71)
  else if n < 62 then Char.ofNat (n - 4)
  else if n = 62 then '-'
  else '_'

/-- Encode bytes, three at a time into four characters, with a
    short last group and no padding. -/
def encode : List UInt8 → List Char
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    char (n / 262144) :: char (n / 4096 % 64) :: char (n / 64 % 64) :: char (n % 64) ::
      encode rest
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [char (n / 262144), char (n / 4096 % 64), char (n / 64 % 64)]
  | [a] =>
    let n := a.toNat * 65536
    [char (n / 262144), char (n / 4096 % 64)]
  | [] => []

/-- The value of one character of the alphabet. -/
def value (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 71)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat + 4)
  else if c = '-' then some 62
  else if c = '_' then some 63
  else none

/-- Decode, four characters at a time into three bytes. A short
    last group of two or three characters gives one or two bytes,
    and its unused bits must be zero. -/
def decode : List Char → Option (List UInt8)
  | [] => some []
  | [c0, c1] =>
    match value c0, value c1 with
    | some v0, some v1 =>
      if v1 % 16 = 0 then some [(v0 * 4 + v1 / 16).toUInt8] else none
    | _, _ => none
  | [c0, c1, c2] =>
    match value c0, value c1, value c2 with
    | some v0, some v1, some v2 =>
      if v2 % 4 = 0 then
        some [(v0 * 4 + v1 / 16).toUInt8, (v1 % 16 * 16 + v2 / 4).toUInt8]
      else none
    | _, _, _ => none
  | c0 :: c1 :: c2 :: c3 :: rest =>
    match value c0, value c1, value c2, value c3, decode rest with
    | some v0, some v1, some v2, some v3, some tail =>
      some ((v0 * 4 + v1 / 16).toUInt8 :: (v1 % 16 * 16 + v2 / 4).toUInt8 ::
        (v2 % 4 * 64 + v3).toUInt8 :: tail)
    | _, _, _, _, _ => none
  | _ => none

end Jws.Base64url

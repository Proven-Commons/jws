/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and
  `bar.toml` records the SHA-256 it had then. The proofs live
  in `Jws.Proofs` (`Jws/Proofs/SpecProofs.lean`); `lake comparator`
  checks that each one proves exactly the statement written
  here. The `sorry` below is expected in this file only.

  The statements use the definitions in `Jws/Token.lean`,
  `Jws/Base64url.lean`, `Jws/Utf8.lean`, and the JSON code
  carried into this repo (`Json/Value.lean` and
  `Json/Parse.lean`), the code under proof named in
  `bar.toml`. The statements about the value of a number also
  use `Jws/Spec/Defs.lean`: the decimal value of a JSON number
  text, written from RFC 8259 separately from the checker's
  own reading. That file is part of the specification too.
-/

import Jws
import Jws.Spec.Defs

open Jws

/-! ## The round trips

The statements the slice stands on. Each one is the statement
of the proved theorem of the same shape in `Jws.Proofs`. -/

/-- Printing a parsed token gives the received text back, byte
    for byte. The two first parts are kept as received, so the
    JWS Signing Input a verifier needs is never rebuilt from the
    JSON values; the signature part is the base64url of the
    signature bytes. -/
theorem Jws.Spec.printToken_parse (s : List Char) (t : Token)
    (h : parseToken s = some t) :
    printToken t = s := sorry

/-- What the parser reads: the received text splits at its dots
    into exactly three parts, the kept header part, the kept
    payload part, and the base64url of the signature bytes; the
    header and claims values are what the two kept parts decode
    to through the base64url decoder, the UTF-8 decoder, and the
    JSON parser. So a parser that kept the right parts but made
    up the values fails this statement. Each of the two decoders
    accepts only its encoder's output: see `Jws.Spec.encode_decode`
    and `Jws.Spec.utf8_encode_decode` below. -/
theorem Jws.Spec.parseToken_reads (s : List Char) (t : Token)
    (h : parseToken s = some t) :
    splitSep '.' s = [t.headerSeg, t.payloadSeg, Base64url.encode t.sig] ∧
    (∃ hb hcs, Base64url.decode t.headerSeg = some hb ∧
      Utf8.decode hb = some hcs ∧ Json.parse hcs = some t.header) ∧
    (∃ pb pcs, Base64url.decode t.payloadSeg = some pb ∧
      Utf8.decode pb = some pcs ∧ Json.parse pcs = some t.claims) := sorry

/-- Parsing the printed form of a token made from header and
    claims values (each written in the JSON printer's canonical
    form) gives that token back, for values that are well formed
    in the JSON slice's sense. So a printer that wrote nothing, or
    wrote something shorter, fails this statement. -/
theorem Jws.Spec.parseToken_print (h c : Json.Json) (sig : List UInt8)
    (hh : Json.WF h) (hc : Json.WF c) :
    parseToken (printToken (makeToken h c sig)) = some (makeToken h c sig) := sorry

/-- Decoding the base64url encoding of any bytes gives the
    bytes back. -/
theorem Jws.Spec.decode_encode (bs : List UInt8) :
    Base64url.decode (Base64url.encode bs) = some bs := sorry

/-! ## Strict decoding

Each decoder accepts only an input that is the encoding of what
it returns. With the round trips, the base64url decoder and the
UTF-8 decoder are exactly the inverses of their encoders: no
padding, no nonzero unused bits, no overlong form, no surrogate,
nothing above U+10FFFF. -/

/-- Encoding what the base64url decoder returned gives the text
    back: the decoder accepts only the canonical, unpadded
    encoding of the bytes it returns. -/
theorem Jws.Spec.encode_decode (cs : List Char) (bs : List UInt8)
    (h : Base64url.decode cs = some bs) :
    Base64url.encode bs = cs := sorry

/-- Decoding the UTF-8 encoding of any text gives the text
    back. -/
theorem Jws.Spec.utf8_decode_encode (cs : List Char) :
    Utf8.decode (Utf8.encode cs) = some cs := sorry

/-- Encoding what the UTF-8 decoder returned gives the bytes
    back: the decoder accepts only what `Utf8.encode` writes for
    the text it returns. That `Utf8.encode` writes the standard
    encoding (RFC 3629) is not stated here. -/
theorem Jws.Spec.utf8_encode_decode (bs : List UInt8) (cs : List Char)
    (h : Utf8.decode bs = some cs) :
    Utf8.encode cs = bs := sorry

/-- The UTF-8 decoder turns away, among others: the overlong
    forms C0 80, E0 80 80 and F0 80 80 80; the encoded surrogate
    ED A0 80; F4 90 80 80, above U+10FFFF; a stray continuation
    byte 80; the truncated E2 82; and the five byte lead F8. -/
theorem Jws.Spec.utf8_rejects_ill_formed :
    ([[0xC0, 0x80], [0xE0, 0x80, 0x80], [0xF0, 0x80, 0x80, 0x80],
      [0xED, 0xA0, 0x80], [0xF4, 0x90, 0x80, 0x80], [0x80], [0xE2, 0x82],
      [0xF8, 0x88, 0x80, 0x80, 0x80]] : List (List UInt8)).all
      (fun bs => (Utf8.decode bs).isNone) = true := sorry

/-! ## Single tokens, accepted and refused

Single inputs run through the same two entry points the
command line tool calls, `parseToken` and `accept`, each with
the context the test harness gives that case. Each input is
one of the named fixed cases in the test harness. The
differential tests cover these rules on many more inputs;
these statements pin them so a reader of the specification
can check each rule against one concrete case. -/

/-- The RFC 7515 A.1 token is accepted when HS256 is allowed
    and the issuer must be `joe`, with no current time
    supplied, so the time comparisons are skipped and the type
    rules still hold. The harness case is "A.1 accept (no time
    checks, issuer checked)". -/
theorem Jws.Spec.accepts_rfc_a1 :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := none, required := [],
           issuer := some "joe".toList, audience := none }
     | none => false) = true := sorry

/-- A hand built token is accepted: header `{"alg":"HS256"}`,
    claims `{"iss":"joe","exp":2000000000}`, a 32 byte
    signature, HS256 allowed, the current time 1500000000
    before the expiry, and the issuer required to be `joe`.
    The harness case is "base accept". -/
theorem Jws.Spec.accepts_hand_built :
    (match parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1500000000,
           required := [], issuer := some "joe".toList,
           audience := none }
     | none => false) = true := sorry

/-- The RFC 7515 A.5 unsecured token (algorithm `none`, empty
    signature part) is refused when HS256 is the allowed
    algorithm. The harness case is "A.5 reject (alg none,
    HS256 allowed)". -/
theorem Jws.Spec.rejects_unsecured_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-- The A.5 token is refused when the allowlist itself names
    `none`: such a context refuses every token. The harness
    case is "A.5 reject (alg none, allowlist names none)". -/
theorem Jws.Spec.rejects_unsecured_none_when_allowlist_names_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["none".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-- The A.5 token is refused when the allowlist names `none`
    alongside HS256. The harness case is "A.5 reject (alg
    none, allowlist names none and HS256)". -/
theorem Jws.Spec.rejects_unsecured_none_when_allowlist_mixes_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["none".toList, "HS256".toList],
           now := some 1300819000, required := [], issuer := none,
           audience := none }
     | none => false) = false := sorry

/-- The A.1 token with its signature part emptied is refused,
    under a context that accepts the token as it stands:
    HS256 allowed, the current time before the expiry, the
    issuer required to be `joe`. The harness case is "A.1
    reject (signature part emptied, otherwise passing
    context)", the case the 2026-10-27 review change pinned. -/
theorem Jws.Spec.rejects_empty_signature :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1300819000,
           required := [], issuer := some "joe".toList,
           audience := none }
     | none => false) = false := sorry

/-- The A.1 token is refused when its algorithm, HS256, is
    outside the allowlist, here RS256 alone. The harness case
    is "A.1 reject (alg not allowed)". -/
theorem Jws.Spec.rejects_alg_outside_allowlist :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".toList with
     | some t => accept t
         { allow := ["RS256".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-- A token whose first part carries a padding character does
    not parse at all: `=` is not in the base64url alphabet,
    and padding is not part of the compact form. The harness
    case is "mutation: padding on header part", built on its
    hand built token. -/
theorem Jws.Spec.rejects_part_not_base64url :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9=.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).isSome
      = false := sorry

/-- A token whose protected (header) part decodes to a JSON
    array, not an object, is refused: the header `["HS256"]`
    on the harness's hand built payload and signature, under
    its base context. The harness case is "mutation: header
    is an array". -/
theorem Jws.Spec.rejects_header_not_object :
    (match parseToken
      "WyJIUzI1NiJd.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1500000000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-! ## Repeated member names

RFC 7515 section 4 (and step 4 of section 5.2) asks a reader of a
header that repeats a parameter name either to turn it away or to
use the last copy; RFC 7519 section 4 asks the same of the claims
set. This slice turns such a token away. -/

/-- An accepted token has a JSON object for its header and for its
    claims, and neither object repeats a member name. Members of
    objects nested inside them are not covered. -/
theorem Jws.Spec.accept_names_unique (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup := sorry

/-- The token whose header is `{"alg":"HS256","alg":"none"}`, with
    claims `{"exp":2000000000}` and signature bytes 01 02 03,
    parses (the parser keeps both copies) and is refused under
    every context. The harness case is "duplicate alg (HS256 then
    none): refused". -/
theorem Jws.Spec.rejects_duplicate_alg (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImFsZyI6Im5vbmUifQ.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false := sorry

/-- The token whose claims are
    `{"iss":"joe","exp":2000000000,"iss":"evil"}`, under the header
    `{"alg":"HS256"}` and signature bytes 01 02 03, parses and is
    refused under every context. The harness case is "duplicate
    iss (joe then evil): refused". -/
theorem Jws.Spec.rejects_duplicate_iss (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImlzcyI6ImV2aWwifQ.AQID".toList
        = some t ∧ accept t ctx = false := sorry

/-! ## The `crit` header parameter

RFC 7515 section 4.1.11: when `crit` lists an extension the
reader does not understand, the JWS is invalid. This slice
understands no extension, so it turns away every header that has
a `crit` member, whatever its value. -/

/-- An accepted token's header is an object with no `crit`
    member. -/
theorem Jws.Spec.accept_no_crit (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs, t.header = .obj hkvs ∧ "crit".toList ∉ hkvs.map Prod.fst := sorry

/-- The token whose header is
    `{"alg":"HS256","b64":false,"crit":["b64"]}` (RFC 7797's
    unencoded payload option, which changes what the signature
    covers), with claims `{"exp":2000000000}` and signature bytes
    01 02 03, parses and is refused under every context. The
    harness case is "crit naming b64: refused". -/
theorem Jws.Spec.rejects_crit_b64 (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImI2NCI6ZmFsc2UsImNyaXQiOlsiYjY0Il19.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false := sorry

/-! ## The audience claim when no audience is expected

RFC 7519 section 4.1.3: when `aud` is present and the reader does
not identify itself with a value in it, the token must be
rejected. A caller that gives no expected audience identifies
itself with none, so such a token is turned away. -/

/-- The token with claims
    `{"iss":"joe","exp":2000000000,"aud":"other-tenant"}`, header
    `{"alg":"HS256"}` and signature bytes 01 02 03 parses and is
    refused when HS256 is allowed, the current time is 1500000000,
    the issuer must be `joe`, and no audience is expected. The
    harness case is "aud present, no audience expected:
    refused". -/
theorem Jws.Spec.rejects_aud_without_audience :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImF1ZCI6Im90aGVyLXRlbmFudCJ9.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 1500000000, required := [],
          issuer := some "joe".toList, audience := none })
      = some false := sorry

/-- The same token is accepted under the same context when the
    expected audience is `other-tenant`, so the refusal above
    comes from the audience rule alone. The harness case is "aud
    present, the same audience expected: accepted". -/
theorem Jws.Spec.accepts_aud_with_audience :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImF1ZCI6Im90aGVyLXRlbmFudCJ9.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 1500000000, required := [],
          issuer := some "joe".toList, audience := some "other-tenant".toList })
      = some true := sorry

/-! ## Fractional NumericDates

RFC 7519 section 2 lets a NumericDate be a non-integer. The check
compares such a value exactly with the current time. -/

/-- The token with claims `{"exp":2000000000.5}`, header
    `{"alg":"HS256"}` and signature bytes 01 02 03 parses and is
    accepted at the current time 2000000000, half a second before
    it expires, with HS256 allowed. The harness case is
    "fractional exp, now half a second before: accepted". -/
theorem Jws.Spec.accepts_fractional_exp_before :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOjIwMDAwMDAwMDAuNX0.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 2000000000, required := [],
          issuer := none, audience := none })
      = some true := sorry

/-- The same token is refused one second later, at 2000000001,
    after it has expired. The harness case is "fractional exp, now
    half a second after: refused". -/
theorem Jws.Spec.rejects_fractional_exp_after :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOjIwMDAwMDAwMDAuNX0.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 2000000001, required := [],
          issuer := none, audience := none })
      = some false := sorry

/-! ## The value of a date claim

The date rules compare the current time with the number an `exp`
or `nbf` claim holds, through the checker's exact decimal reading
`numVal` and its comparison `NumVal.cmp`. These statements tie
both to the decimal value of the number text, defined in
`Jws/Spec/Defs.lean` from the JSON grammar: `numberText` builds a text
from its pieces, `digitsValue` and `expValue` give the value of
the digits and of the exponent part, and `atBase` writes a decimal
as a whole number over a chosen power of ten. -/

/-- `NumVal.cmp` compares the exact values of two number values:
    over any power of ten `10^m` with `m` at most both exponents,
    it is the comparison of the two values written as whole
    numbers over `10^m`. -/
theorem Jws.Spec.cmp_exact (a b : NumVal) (m : Int) (ha : m ≤ a.exp) (hb : m ≤ b.exp) :
    NumVal.cmp a b = compare (atBase a.neg a.sig a.exp m) (atBase b.neg b.sig b.exp m) := sorry

/-- `numVal` reads every number text of the JSON grammar (an
    optional minus sign, one or more integer digits, optional
    fraction digits after a point, an optional exponent part),
    and what it returns has the text's decimal value: the sign,
    the integer and fraction digits read as one whole number, and
    ten to the exponent less the count of fraction digits. -/
theorem Jws.Spec.numVal_value (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      ∀ m, m ≤ v.exp → m ≤ expValue ex - frac.length →
        atBase v.neg v.sig v.exp m =
          atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length) m := sorry

/-- The comparison the `exp` and `nbf` rules make, between the
    current time `now` (`NumVal.ofInt now`) and a claim's number
    text of the JSON grammar, is the exact comparison of the whole
    number `now` with the text's decimal value: both are written
    as whole numbers over `10^m`, where `m` is the smaller of zero
    and the text's exponent less its count of fraction digits. -/
theorem Jws.Spec.numVal_cmp_now (now : Int) (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      NumVal.cmp (NumVal.ofInt now) v =
        compare (now * 10 ^ (-(min 0 (expValue ex - frac.length))).toNat)
          (atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length)
            (min 0 (expValue ex - frac.length))) := sorry

/-- The harness's hand built token with claims `{"exp":-1}` (header
    `{"alg":"HS256"}`, its 32 byte signature) is refused at the
    current time 0, with HS256 allowed: it expired a second before.
    A reading that dropped the minus sign would accept it. The
    harness case is "mutation: negative exp, now zero (reject)". -/
theorem Jws.Spec.rejects_negative_exp :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOi0xfQ.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 0, required := [],
          issuer := none, audience := none })
      = some false := sorry

/-- The same header and signature with claims `{"exp":-0.5}` are
    accepted at the current time -1, half a second before the
    expiry. The harness case is "exp a negative fraction -0.5, now
    -1: accepted". -/
theorem Jws.Spec.accepts_negative_fraction_exp :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOi0wLjV9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some (-1), required := [],
          issuer := none, audience := none })
      = some true := sorry

/-! ## What acceptance means

The plan's main claim: a token is accepted only when its header
`alg` is on the allowlist and its registered claims pass the
checks. One statement collects every rule the check applies. -/

/-- When the check accepts a token, under any context: the
    allowlist does not name `none`; the signature is not empty;
    the header and the claims are JSON objects with no repeated
    member name; the header has no `crit` member; the header's
    `alg` is a string other than `none` that is on the allowlist;
    every required claim is present; `exp`, `nbf` and `iat`, when
    present, are numbers the checker reads with `numVal`, with
    the current time before `exp` and not before `nbf` under
    `NumVal.cmp` when a time is given (the statements in the
    section above say these are the exact decimal values); `iss`,
    when present, is a string; `aud`, when present, is a string
    or an array of strings; the issuer is the expected
    one when one is given; and `aud` is absent when no audience is
    expected, or names the expected audience when one is. A
    program that accepts nothing meets this statement; the
    accepting statements above are what rule it out. -/
theorem Jws.Spec.accept_sound (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    "none".toList ∉ ctx.allow ∧ t.sig ≠ [] ∧
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup ∧
      "crit".toList ∉ hkvs.map Prod.fst ∧
      (∃ alg, ("alg".toList, Json.Json.str alg) ∈ hkvs ∧
        alg ≠ "none".toList ∧ alg ∈ ctx.allow) ∧
      (∀ n ∈ ctx.required, n ∈ ckvs.map Prod.fst) ∧
      (∀ v, ("exp".toList, v) ∈ ckvs → ∃ cs e, v = .num cs ∧ numVal cs = some e ∧
        ∀ now, ctx.now = some now → NumVal.cmp (NumVal.ofInt now) e = .lt) ∧
      (∀ v, ("nbf".toList, v) ∈ ckvs → ∃ cs e, v = .num cs ∧ numVal cs = some e ∧
        ∀ now, ctx.now = some now → NumVal.cmp (NumVal.ofInt now) e ≠ .lt) ∧
      (∀ v, ("iat".toList, v) ∈ ckvs → ∃ cs e, v = .num cs ∧ numVal cs = some e) ∧
      (∀ v, ("iss".toList, v) ∈ ckvs → ∃ s, v = .str s) ∧
      (∀ v, ("aud".toList, v) ∈ ckvs →
        (∃ s, v = .str s) ∨ ∃ vs, v = .arr vs ∧ ∀ x ∈ vs, ∃ s, x = .str s) ∧
      (∀ i, ctx.issuer = some i → ("iss".toList, Json.Json.str i) ∈ ckvs) ∧
      (ctx.audience = none → "aud".toList ∉ ckvs.map Prod.fst) ∧
      (∀ a, ctx.audience = some a →
        ("aud".toList, Json.Json.str a) ∈ ckvs ∨
        ∃ vs, ("aud".toList, Json.Json.arr vs) ∈ ckvs ∧ Json.Json.str a ∈ vs) := sorry

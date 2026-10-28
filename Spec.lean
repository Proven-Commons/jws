/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and
  `bar.toml` records the SHA-256 it had then. The proofs live
  in `Proofs` (`Proofs/SpecProofs.lean`); `lake comparator`
  checks that each one proves exactly the statement written
  here. The `sorry` below is expected in this file only.

  The statements use only the definitions in `Jws/Token.lean`,
  `Jws/Base64url.lean`, `Jws/Utf8.lean`, and the JSON code
  carried into this repo (`Json/Value.lean` and
  `Json/Parse.lean`), the code under proof named in
  `bar.toml`. No definition of their own is needed, so this
  project has no `Spec/Defs.lean`.
-/

import Jws

open Jws

/-! ## The round trips

The statements the slice stands on. Each one is the statement
of the proved theorem of the same shape in `Proofs`. -/

/-- Printing a parsed token gives the received text back, byte
    for byte. The two first parts are kept as received, so the
    JWS Signing Input a verifier needs is never rebuilt from the
    JSON values; the signature part is the base64url of the
    signature bytes. The command line tool answers an accepted
    token with this print. -/
theorem Spec.printToken_parse (s : List Char) (t : Token)
    (h : parseToken s = some t) :
    printToken t = s := sorry

/-- What the parser reads: the received text splits at its dots
    into exactly three parts, the kept header part, the kept
    payload part, and the base64url of the signature bytes; the
    header and claims values are what the two kept parts decode
    to through strict base64url, strict UTF-8, and the JSON
    parser. So a parser that kept the right parts but made up the
    values fails this statement. -/
theorem Spec.parseToken_reads (s : List Char) (t : Token)
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
theorem Spec.parseToken_print (h c : Json.Json) (sig : List UInt8)
    (hh : Json.WF h) (hc : Json.WF c) :
    parseToken (printToken (makeToken h c sig)) = some (makeToken h c sig) := sorry

/-- Decoding the base64url encoding of any bytes gives the
    bytes back. -/
theorem Spec.decode_encode (bs : List UInt8) :
    Base64url.decode (Base64url.encode bs) = some bs := sorry

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
theorem Spec.accepts_rfc_a1 :
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
theorem Spec.accepts_hand_built :
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
theorem Spec.rejects_unsecured_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-- The A.5 token is refused when the allowlist itself names
    `none`: such a context refuses every token. The harness
    case is "A.5 reject (alg none, allowlist names none)". -/
theorem Spec.rejects_unsecured_none_when_allowlist_names_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["none".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := sorry

/-- The A.5 token is refused when the allowlist names `none`
    alongside HS256. The harness case is "A.5 reject (alg
    none, allowlist names none and HS256)". -/
theorem Spec.rejects_unsecured_none_when_allowlist_mixes_none :
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
theorem Spec.rejects_empty_signature :
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
theorem Spec.rejects_alg_outside_allowlist :
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
theorem Spec.rejects_part_not_base64url :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9=.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).isSome
      = false := sorry

/-- A token whose protected (header) part decodes to a JSON
    array, not an object, is refused: the header `["HS256"]`
    on the harness's hand built payload and signature, under
    its base context. The harness case is "mutation: header
    is an array". -/
theorem Spec.rejects_header_not_object :
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
theorem Spec.accept_names_unique (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup := sorry

/-- The token whose header is `{"alg":"HS256","alg":"none"}`, with
    claims `{"exp":2000000000}` and signature bytes 01 02 03,
    parses (the parser keeps both copies) and is refused under
    every context. The harness case is "duplicate alg (HS256 then
    none): refused". -/
theorem Spec.rejects_duplicate_alg (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImFsZyI6Im5vbmUifQ.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false := sorry

/-- The token whose claims are
    `{"iss":"joe","exp":2000000000,"iss":"evil"}`, under the header
    `{"alg":"HS256"}` and signature bytes 01 02 03, parses and is
    refused under every context. The harness case is "duplicate
    iss (joe then evil): refused". -/
theorem Spec.rejects_duplicate_iss (ctx : Context) :
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
theorem Spec.accept_no_crit (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs, t.header = .obj hkvs ∧ "crit".toList ∉ hkvs.map Prod.fst := sorry

/-- The token whose header is
    `{"alg":"HS256","b64":false,"crit":["b64"]}` (RFC 7797's
    unencoded payload option, which changes what the signature
    covers), with claims `{"exp":2000000000}` and signature bytes
    01 02 03, parses and is refused under every context. The
    harness case is "crit naming b64: refused". -/
theorem Spec.rejects_crit_b64 (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImI2NCI6ZmFsc2UsImNyaXQiOlsiYjY0Il19.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false := sorry

/-
  Proofs of the statements in `Spec.lean`, under the same
  names.

  The round trips are the theorems proved in
  `Proofs/Token.lean` and `Proofs/B64.lean`; the number
  statements are proved in `Proofs/Num.lean`. The single
  tokens are checked in the kernel with `decide +kernel`: no
  native evaluation, which the bar forbids.
-/

import Jws
import Spec.Defs
import Proofs.Token
import Proofs.B64
import Proofs.Check
import Proofs.Num

open Jws Spec

theorem Spec.printToken_parse (s : List Char) (t : Token)
    (h : parseToken s = some t) :
    printToken t = s :=
  Jws.Proofs.printToken_parse s t h

theorem Spec.parseToken_reads (s : List Char) (t : Token)
    (h : parseToken s = some t) :
    splitSep '.' s = [t.headerSeg, t.payloadSeg, Base64url.encode t.sig] ∧
    (∃ hb hcs, Base64url.decode t.headerSeg = some hb ∧
      Utf8.decode hb = some hcs ∧ Json.parse hcs = some t.header) ∧
    (∃ pb pcs, Base64url.decode t.payloadSeg = some pb ∧
      Utf8.decode pb = some pcs ∧ Json.parse pcs = some t.claims) :=
  Jws.Proofs.parseToken_reads s t h

theorem Spec.parseToken_print (h c : Json.Json) (sig : List UInt8)
    (hh : Json.WF h) (hc : Json.WF c) :
    parseToken (printToken (makeToken h c sig)) = some (makeToken h c sig) :=
  Jws.Proofs.parseToken_print h c sig hh hc

theorem Spec.decode_encode (bs : List UInt8) :
    Base64url.decode (Base64url.encode bs) = some bs :=
  Jws.Base64url.Proofs.decode_encode bs


theorem Spec.accepts_rfc_a1 :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := none, required := [],
           issuer := some "joe".toList, audience := none }
     | none => false) = true := by
  decide +kernel


theorem Spec.accepts_hand_built :
    (match parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1500000000,
           required := [], issuer := some "joe".toList,
           audience := none }
     | none => false) = true := by
  decide +kernel


theorem Spec.rejects_unsecured_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.rejects_unsecured_none_when_allowlist_names_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["none".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.rejects_unsecured_none_when_allowlist_mixes_none :
    (match parseToken
      "eyJhbGciOiJub25lIn0.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["none".toList, "HS256".toList],
           now := some 1300819000, required := [], issuer := none,
           audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.rejects_empty_signature :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1300819000,
           required := [], issuer := some "joe".toList,
           audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.rejects_alg_outside_allowlist :
    (match parseToken
      "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ.dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".toList with
     | some t => accept t
         { allow := ["RS256".toList], now := some 1300819000,
           required := [], issuer := none, audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.rejects_part_not_base64url :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9=.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_header_not_object :
    (match parseToken
      "WyJIUzI1NiJd.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDB9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList with
     | some t => accept t
         { allow := ["HS256".toList], now := some 1500000000,
           required := [], issuer := none, audience := none }
     | none => false) = false := by
  decide +kernel


theorem Spec.accept_names_unique (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup :=
  Jws.Proofs.accept_names_unique t ctx h

theorem Spec.rejects_duplicate_alg (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImFsZyI6Im5vbmUifQ.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false :=
  Jws.Proofs.refused_of_shape _ ctx (by decide +kernel)

theorem Spec.rejects_duplicate_iss (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImlzcyI6ImV2aWwifQ.AQID".toList
        = some t ∧ accept t ctx = false :=
  Jws.Proofs.refused_of_shape _ ctx (by decide +kernel)

theorem Spec.accept_no_crit (t : Token) (ctx : Context)
    (h : accept t ctx = true) :
    ∃ hkvs, t.header = .obj hkvs ∧ "crit".toList ∉ hkvs.map Prod.fst :=
  Jws.Proofs.accept_no_crit t ctx h

theorem Spec.rejects_crit_b64 (ctx : Context) :
    ∃ t, parseToken
      "eyJhbGciOiJIUzI1NiIsImI2NCI6ZmFsc2UsImNyaXQiOlsiYjY0Il19.eyJleHAiOjIwMDAwMDAwMDB9.AQID".toList
        = some t ∧ accept t ctx = false :=
  Jws.Proofs.refused_of_shape _ ctx (by decide +kernel)

theorem Spec.rejects_aud_without_audience :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImF1ZCI6Im90aGVyLXRlbmFudCJ9.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 1500000000, required := [],
          issuer := some "joe".toList, audience := none })
      = some false := by
  decide +kernel

theorem Spec.accepts_aud_with_audience :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImF1ZCI6Im90aGVyLXRlbmFudCJ9.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 1500000000, required := [],
          issuer := some "joe".toList, audience := some "other-tenant".toList })
      = some true := by
  decide +kernel

theorem Spec.accepts_fractional_exp_before :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOjIwMDAwMDAwMDAuNX0.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 2000000000, required := [],
          issuer := none, audience := none })
      = some true := by
  decide +kernel

theorem Spec.rejects_fractional_exp_after :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOjIwMDAwMDAwMDAuNX0.AQID".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 2000000001, required := [],
          issuer := none, audience := none })
      = some false := by
  decide +kernel

theorem Spec.cmp_exact (a b : NumVal) (m : Int) (ha : m ≤ a.exp) (hb : m ≤ b.exp) :
    NumVal.cmp a b = compare (atBase a.neg a.sig a.exp m) (atBase b.neg b.sig b.exp m) :=
  Jws.Proofs.Num.cmp_exact a b m ha hb

theorem Spec.numVal_value (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      ∀ m, m ≤ v.exp → m ≤ expValue ex - frac.length →
        atBase v.neg v.sig v.exp m =
          atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length) m :=
  Jws.Proofs.Num.numVal_value neg ints frac ex hi hf hx

theorem Spec.numVal_cmp_now (now : Int) (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      NumVal.cmp (NumVal.ofInt now) v =
        compare (now * 10 ^ (-(min 0 (expValue ex - frac.length))).toNat)
          (atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length)
            (min 0 (expValue ex - frac.length))) :=
  Jws.Proofs.Num.numVal_cmp_now now neg ints frac ex hi hf hx

theorem Spec.rejects_negative_exp :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOi0xfQ.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some 0, required := [],
          issuer := none, audience := none })
      = some false := by
  decide +kernel

theorem Spec.accepts_negative_fraction_exp :
    (parseToken
      "eyJhbGciOiJIUzI1NiJ9.eyJleHAiOi0wLjV9.AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8".toList).map
      (fun t => accept t
        { allow := ["HS256".toList], now := some (-1), required := [],
          issuer := none, audience := none })
      = some true := by
  decide +kernel

theorem Spec.accept_sound (t : Token) (ctx : Context)
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
        ∃ vs, ("aud".toList, Json.Json.arr vs) ∈ ckvs ∧ Json.Json.str a ∈ vs) :=
  Jws.Proofs.accept_sound t ctx h

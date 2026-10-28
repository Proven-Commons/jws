import Jws.Utf8
import Proofs.B64

namespace Jws.Utf8.Proofs

open Jws.Utf8 Jws.Base64url.Proofs

/-- A character value is below 110000, and no character value
    lies in the surrogate gap D800 to DFFF: the Unicode scalar
    range every `Char` lives in. -/
theorem char_bounds (c : Char) :
    c.toNat < 0x110000 ∧ ¬ (0xD800 ≤ c.toNat ∧ c.toNat < 0xE000) := by
  have h := c.valid
  show c.val.toNat < 0x110000 ∧ ¬ (0xD800 ≤ c.val.toNat ∧ c.val.toNat < 0xE000)
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩

/-- A byte whose value is known to be a continuation byte reads
    back as its payload value. -/
theorem contVal_of_toNat {b : UInt8} {k : Nat} (h : b.toNat = 0x80 + k) (hk : k < 64) :
    contVal b = some k := by
  unfold contVal
  rw [h, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- One step of the decoder on a plain byte. -/
theorem decode_one (b : UInt8) (bs : List UInt8) (hb : b.toNat < 0x80) :
    decode (b :: bs) = (decode bs).map (Char.ofNat b.toNat :: ·) := by
  cases bs with
  | nil => rw [decode.eq_3, if_pos hb]
  | cons b1 bs' => rw [decode.eq_2, if_pos hb]

/-- One step of the decoder on a two byte form. -/
theorem decode_two (b b1 : UInt8) (bs : List UInt8) (v : Nat)
    (hb : 0xC2 ≤ b.toNat ∧ b.toNat < 0xE0) (hv : contVal b1 = some v) :
    decode (b :: b1 :: bs) =
      (decode bs).map (Char.ofNat ((b.toNat - 0xC0) * 64 + v) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_pos (by omega : b.toNat < 0xE0), hv]

/-- One step of the decoder on a three byte form. -/
theorem decode_three (b b1 b2 : UInt8) (bs : List UInt8) (v1 v2 : Nat)
    (hb : 0xE0 ≤ b.toNat ∧ b.toNat < 0xF0)
    (hside : (b.toNat = 0xE0 → 0x20 ≤ v1) ∧ (b.toNat = 0xED → v1 < 0x20))
    (hv1 : contVal b1 = some v1) (hv2 : contVal b2 = some v2) :
    decode (b :: b1 :: b2 :: bs) =
      (decode bs).map (Char.ofNat ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_neg (by omega : ¬ b.toNat < 0xE0),
    if_pos (by omega : b.toNat < 0xF0)]
  dsimp only
  rw [hv1, hv2]
  dsimp only
  rw [if_pos hside]

/-- One step of the decoder on a four byte form. -/
theorem decode_four (b b1 b2 b3 : UInt8) (bs : List UInt8) (v1 v2 v3 : Nat)
    (hb : 0xF0 ≤ b.toNat ∧ b.toNat < 0xF5)
    (hside : (b.toNat = 0xF0 → 0x10 ≤ v1) ∧ (b.toNat = 0xF4 → v1 < 0x10))
    (hv1 : contVal b1 = some v1) (hv2 : contVal b2 = some v2)
    (hv3 : contVal b3 = some v3) :
    decode (b :: b1 :: b2 :: b3 :: bs) =
      (decode bs).map
        (Char.ofNat ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_neg (by omega : ¬ b.toNat < 0xE0),
    if_neg (by omega : ¬ b.toNat < 0xF0), if_pos (by omega : b.toNat < 0xF5)]
  dsimp only
  rw [hv1, hv2, hv3]
  dsimp only
  rw [if_pos hside]

/-- Decoding one encoded character in front of any bytes decodes
    the character and then the bytes. The four cases are the four
    lengths; each one applies the step lemma for its length,
    checks the side conditions with arithmetic, and rebuilds the
    character value. -/
theorem decode_append_char (c : Char) (bs : List UInt8) :
    decode (encodeChar c ++ bs) = (decode bs).map (c :: ·) := by
  obtain ⟨hmax, hnsur⟩ := char_bounds c
  by_cases h1 : c.toNat < 0x80
  · rw [encodeChar, if_pos h1, List.cons_append, List.nil_append,
      decode_one _ _ (by rw [toNat_toUInt8 (by omega)]; exact h1),
      toNat_toUInt8 (by omega), Char.ofNat_toNat]
  · rw [encodeChar, if_neg h1]
    by_cases h2 : c.toNat < 0x800
    · have hlead : (0xC0 + c.toNat / 64).toUInt8.toNat = 0xC0 + c.toNat / 64 :=
        toNat_toUInt8 (by omega)
      rw [if_pos h2, List.cons_append, List.cons_append, List.nil_append,
        decode_two _ _ _ _ ⟨by omega, by omega⟩
          (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
        hlead,
        show (0xC0 + c.toNat / 64 - 0xC0) * 64 + c.toNat % 64 = c.toNat by omega,
        Char.ofNat_toNat]
    · rw [if_neg h2]
      by_cases h3 : c.toNat < 0x10000
      · have hlead : (0xE0 + c.toNat / 4096).toUInt8.toNat = 0xE0 + c.toNat / 4096 :=
          toNat_toUInt8 (by omega)
        rw [if_pos h3, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append,
          decode_three _ _ _ _ _ _ ⟨by omega, by omega⟩
            ⟨fun hb => by rw [hlead] at hb; omega,
             fun hb => by rw [hlead] at hb; omega⟩
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
          hlead,
          show (0xE0 + c.toNat / 4096 - 0xE0) * 4096 + (c.toNat / 64) % 64 * 64 +
            c.toNat % 64 = c.toNat by omega,
          Char.ofNat_toNat]
      · have hlead : (0xF0 + c.toNat / 262144).toUInt8.toNat = 0xF0 + c.toNat / 262144 :=
          toNat_toUInt8 (by omega)
        rw [if_neg h3, List.cons_append, List.cons_append, List.cons_append,
          List.cons_append, List.nil_append,
          decode_four _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩
            ⟨fun hb => by rw [hlead] at hb; omega,
             fun hb => by rw [hlead] at hb; omega⟩
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
          hlead,
          show (0xF0 + c.toNat / 262144 - 0xF0) * 262144 + (c.toNat / 4096) % 64 * 4096 +
            (c.toNat / 64) % 64 * 64 + c.toNat % 64 = c.toNat by omega,
          Char.ofNat_toNat]

/-- Decoding the encoding of any text gives the text back. -/
theorem decode_encode : ∀ cs : List Char, decode (encode cs) = some cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show decode (encodeChar c ++ encode cs) = some (c :: cs)
    rw [decode_append_char, ih]
    rfl


/-- A byte `contVal` reads is a continuation byte with that payload. -/
theorem contVal_spec {b : UInt8} {v : Nat} (h : contVal b = some v) :
    b.toNat = 0x80 + v ∧ v < 64 := by
  unfold contVal at h
  split at h
  · rename_i hb; have := Option.some.inj h; omega
  · cases h

/-- A Unicode scalar value is the code of the character made from it. -/
theorem toNat_ofNat_valid {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  rw [Char.ofNat, dite_eq_left h]; rfl

/-- A number equal to a byte's value converts to that byte. -/
theorem u8_eq {k : Nat} {b : UInt8} (h : k = b.toNat) : k.toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  rw [toNat_toUInt8 (by have := b.toNat_lt; omega)]
  exact h

/-- The converse round trip, by strong induction on the byte count:
    each branch of the decoder that succeeds read the bytes the
    encoder writes for the character it made. -/
theorem encode_decode_lt : ∀ (n : Nat) (bs : List UInt8), bs.length < n →
    ∀ cs, decode bs = some cs → encode cs = bs
  | 0, _, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | _ + 1, [], _, cs, h => by
    rw [decode.eq_1] at h; cases h; rfl
  | n + 1, b :: rest, hl, cs, h => by
    rw [decode.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hb
      obtain ⟨cs', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      show encodeChar _ ++ encode cs' = b :: rest
      rw [encode_decode_lt n rest (by simp at hl; omega) cs' h1]
      have hv : (Char.ofNat b.toNat).toNat = b.toNat := toNat_ofNat_valid (by left; omega)
      unfold encodeChar
      rw [hv, ite_eq_left hb, u8_eq rfl]
      rfl
    · split at h
      · cases h
      · split at h
        · split at h
          · split at h
            · rename_i h0 h1 h2 _ b1 rest1 _ v1 hv1
              obtain ⟨cs', h1', rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨hb1, hv⟩ := contVal_spec hv1
              show encodeChar _ ++ encode cs' = b :: b1 :: rest1
              rw [encode_decode_lt n rest1 (by simp at hl; omega) cs' h1']
              generalize hN : (b.toNat - 192) * 64 + v1 = N
              have hc : (Char.ofNat N).toNat = N := toNat_ofNat_valid (by left; omega)
              unfold encodeChar
              rw [hc, ite_eq_right (by omega), ite_eq_left (by omega),
                show (0xC0 + N / 64).toUInt8 = b from u8_eq (by omega),
                show (0x80 + N % 64).toUInt8 = b1 from u8_eq (by omega)]
              rfl
            · cases h
          · cases h
        · split at h
          · split at h
            · split at h
              · split at h
                · rename_i h0 h1 h2 h3 _ b1 b2 rest1 _ _ v1 v2 hv1 hv2 hside
                  obtain ⟨cs', h1', rfl⟩ := Option.map_eq_some_iff.mp h
                  obtain ⟨hb1, hv1'⟩ := contVal_spec hv1
                  obtain ⟨hb2, hv2'⟩ := contVal_spec hv2
                  obtain ⟨hs1, hs2⟩ := hside
                  show encodeChar _ ++ encode cs' = b :: b1 :: b2 :: rest1
                  rw [encode_decode_lt n rest1 (by simp at hl; omega) cs' h1']
                  generalize hN : (b.toNat - 224) * 4096 + v1 * 64 + v2 = N
                  have hc : (Char.ofNat N).toNat = N := toNat_ofNat_valid (by
                    by_cases hb : b.toNat ≤ 237
                    · left; omega
                    · right; omega)
                  unfold encodeChar
                  rw [hc, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
                    show (0xE0 + N / 4096).toUInt8 = b from u8_eq (by omega),
                    show (0x80 + N / 64 % 64).toUInt8 = b1 from u8_eq (by omega),
                    show (0x80 + N % 64).toUInt8 = b2 from u8_eq (by omega)]
                  rfl
                · cases h
              · cases h
            · cases h
          · split at h
            · split at h
              · split at h
                · split at h
                  · rename_i h0 h1 h2 h3 h4 _ b1 b2 b3 rest1 _ _ _ v1 v2 v3 hv1 hv2 hv3 hside
                    obtain ⟨cs', h1', rfl⟩ := Option.map_eq_some_iff.mp h
                    obtain ⟨hb1, hv1'⟩ := contVal_spec hv1
                    obtain ⟨hb2, hv2'⟩ := contVal_spec hv2
                    obtain ⟨hb3, hv3'⟩ := contVal_spec hv3
                    obtain ⟨hs1, hs2⟩ := hside
                    show encodeChar _ ++ encode cs' = b :: b1 :: b2 :: b3 :: rest1
                    rw [encode_decode_lt n rest1 (by simp at hl; omega) cs' h1']
                    generalize hN : (b.toNat - 240) * 262144 + v1 * 4096 + v2 * 64 + v3 = N
                    have hc : (Char.ofNat N).toNat = N := toNat_ofNat_valid (by
                      right
                      by_cases hb : b.toNat = 240
                      · omega
                      · by_cases hb' : b.toNat = 244
                        · omega
                        · omega)
                    unfold encodeChar
                    rw [hc, ite_eq_right (by omega), ite_eq_right (by omega),
                      ite_eq_right (by omega),
                      show (0xF0 + N / 262144).toUInt8 = b from u8_eq (by omega),
                      show (0x80 + N / 4096 % 64).toUInt8 = b1 from u8_eq (by omega),
                      show (0x80 + N / 64 % 64).toUInt8 = b2 from u8_eq (by omega),
                      show (0x80 + N % 64).toUInt8 = b3 from u8_eq (by omega)]
                    rfl
                  · cases h
                · cases h
              · cases h
            · cases h

/-- Encoding a decoding gives the bytes back: the decoder accepts only
    byte strings that `encode` writes for the text it returns. -/
theorem encode_decode (bs : List UInt8) (cs : List Char) (h : decode bs = some cs) :
    encode cs = bs :=
  encode_decode_lt _ bs (Nat.lt_succ_self _) cs h

end Jws.Utf8.Proofs

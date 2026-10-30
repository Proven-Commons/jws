import Jws.Base64url

open Jws.Base64url

namespace Jws.Base64url.Proofs

theorem charLe (a c : Char) : a ≤ c ↔ a.toNat ≤ c.toNat := by
  simp [Char.le_def, UInt32.le_iff_toNat_le]

set_option maxRecDepth 10000 in
/-- The finite table check, delegated to the kernel: every value
    below 64 reads back through the alphabet. -/
theorem value_tbl : ∀ n : Fin 64, value (char n.val) = some n.val := by
  decide +kernel

theorem value_char {n : Nat} (h : n < 64) : value (char n) = some n :=
  value_tbl ⟨n, h⟩

/-- The dot that joins the parts is never a character of the
    encoding. The token round trip proof needs this. -/
theorem char_ne_dot {n : Nat} (h : n < 64) : char n ≠ '.' := by
  intro e
  have hv : value '.' = none := by decide
  have hvc := value_char h
  rw [e, hv] at hvc
  cases hvc

set_option maxRecDepth 10000 in
theorem upper_tbl : ∀ k : Fin 26, (char k.val).toNat = k.val + 65 := by decide +kernel
set_option maxRecDepth 10000 in
theorem lower_tbl : ∀ k : Fin 26, (char (k.val + 26)).toNat = k.val + 97 := by decide +kernel
set_option maxRecDepth 10000 in
theorem digit_tbl : ∀ k : Fin 10, (char (k.val + 52)).toNat = k.val + 48 := by decide +kernel
theorem char_62 : char 62 = '-' := by decide +kernel
theorem char_63 : char 63 = '_' := by decide +kernel

/-- Anything the decoder accepts is a character the encoder
    writes, with the same value. -/
theorem value_some {c : Char} {v : Nat} (h : value c = some v) :
    v < 64 ∧ char v = c := by
  unfold value at h
  simp only [charLe] at h
  have hA : 'A'.toNat = 65 := rfl
  have hZ : 'Z'.toNat = 90 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hz : 'z'.toNat = 122 := rfl
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  rw [hA, hZ, ha, hz, h0, h9] at h
  split at h
  · rename_i hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have htb := upper_tbl ⟨c.toNat - 65, by omega⟩
    simp only at htb
    rw [htb]; omega
  split at h
  · rename_i _ hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have htb := lower_tbl ⟨c.toNat - 97, by omega⟩
    simp only at htb
    have e : c.toNat - 97 + 26 = c.toNat - 71 := by omega
    rw [e] at htb
    rw [htb]; omega
  split at h
  · rename_i _ _ hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have htb := digit_tbl ⟨c.toNat - 48, by omega⟩
    simp only at htb
    have e : c.toNat - 48 + 52 = c.toNat + 4 := by omega
    rw [e] at htb
    rw [htb]; omega
  split at h
  · rename_i hc
    cases h; subst hc; exact ⟨by omega, char_62⟩
  split at h
  · rename_i hc
    cases h; subst hc; exact ⟨by omega, char_63⟩
  · cases h

theorem toNat_toUInt8 {k : Nat} (h : k < 256) : k.toUInt8.toNat = k := by
  simp; omega

/-- Decoding the encoding of any bytes gives the bytes back. -/
theorem decode_encode : ∀ bs : List UInt8, decode (encode bs) = some bs := by
  intro bs
  induction bs using encode.induct with
  | case1 a b c rest ih =>
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    have hc := UInt8.toNat_lt c
    rw [encode.eq_1, decode.eq_4, value_char (by omega), value_char (by omega),
      value_char (by omega), value_char (by omega), ih]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case2 a b =>
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    rw [encode.eq_2, decode.eq_3, value_char (by omega), value_char (by omega),
      value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case3 a =>
    have ha := UInt8.toNat_lt a
    rw [encode.eq_3, decode.eq_2, value_char (by omega), value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp; rw [toNat_toUInt8 (by omega)]; omega
  | case4 => rfl

/-- Encoding the decoding of a text the decoder accepted gives
    the text back. -/
theorem encode_decode : ∀ (cs : List Char) (bs : List UInt8),
    decode cs = some bs → encode bs = cs := by
  intro cs bs
  induction cs using decode.induct generalizing bs with
  | case1 =>
    intro h
    rw [decode.eq_1, Option.some.injEq] at h
    subst h; rfl
  | case2 c0 c1 v0 v1 h1 h0 hm =>
    intro h
    rw [decode.eq_2, h0, h1] at h
    simp only [ite_eq_left hm, Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    rw [encode.eq_3, toNat_toUInt8 (by omega)]
    have e1 : (v0 * 4 + v1 / 16) * 65536 / 262144 = v0 := by omega
    have e2 : (v0 * 4 + v1 / 16) * 65536 / 4096 % 64 = v1 := by omega
    rw [e1, e2, ch0, ch1]
  | case3 c0 c1 v0 v1 h1 h0 hm =>
    intro h
    rw [decode.eq_2, h0, h1] at h
    simp only [ite_eq_right hm] at h
    cases h
  | case4 c0 c1 hn =>
    intro h
    rw [decode.eq_2] at h
    split at h
    · exact (hn _ _ ‹_› ‹_›).elim
    · cases h
  | case5 c0 c1 c2 v0 v1 v2 h2 h1 h0 hm =>
    intro h
    rw [decode.eq_3, h0, h1, h2] at h
    simp only [ite_eq_left hm, Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    obtain ⟨lt2, ch2⟩ := value_some h2
    rw [encode.eq_2, toNat_toUInt8 (by omega), toNat_toUInt8 (by omega)]
    have e1 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 262144 =
        v0 := by omega
    have e2 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 4096 % 64 =
        v1 := by omega
    have e3 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 64 % 64 =
        v2 := by omega
    rw [e1, e2, e3, ch0, ch1, ch2]
  | case6 c0 c1 c2 v0 v1 v2 h2 h1 h0 hm =>
    intro h
    rw [decode.eq_3, h0, h1, h2] at h
    simp only [ite_eq_right hm] at h
    cases h
  | case7 c0 c1 c2 hn =>
    intro h
    rw [decode.eq_3] at h
    split at h
    · exact (hn _ _ _ ‹_› ‹_› ‹_›).elim
    · cases h
  | case8 c0 c1 c2 c3 rest v0 v1 v2 v3 tail hrec h3 h2 h1 h0 ih =>
    intro h
    rw [decode.eq_4, h0, h1, h2, h3, hrec] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    obtain ⟨lt2, ch2⟩ := value_some h2
    obtain ⟨lt3, ch3⟩ := value_some h3
    rw [encode.eq_1, toNat_toUInt8 (by omega), toNat_toUInt8 (by omega),
      toNat_toUInt8 (by omega), ih tail hrec]
    have e1 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 262144 = v0 := by omega
    have e2 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 4096 % 64 = v1 := by omega
    have e3 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 64 % 64 = v2 := by omega
    have e4 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) % 64 = v3 := by omega
    rw [e1, e2, e3, e4, ch0, ch1, ch2, ch3]
  | case9 c0 c1 c2 c3 rest hn ih =>
    intro h
    rw [decode.eq_4] at h
    split at h
    · exact (hn _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›).elim
    · cases h
  | case10 t h0 h1 h2 h3 =>
    intro h
    rw [decode.eq_5 _ h0 h1 h2 h3] at h
    cases h

end Jws.Base64url.Proofs

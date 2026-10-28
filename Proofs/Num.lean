import Jws.Token
import Spec.Defs
import Proofs.RoundTrip

/-
  Proofs about the checker's exact decimal reading of claim numbers:
  `NumVal.cmp` compares exact values, `numVal` reads a number text
  of the JSON grammar as its decimal value, and the comparison the
  date rules make between the current time and a claim is the exact
  comparison of the two values.
-/

namespace Jws.Proofs.Num

open Jws Spec

/-! ## Comparisons -/

theorem compare_of_lt {a b : Nat} (h : a < b) : compare a b = .lt := Nat.compare_eq_lt.mpr h
theorem compare_of_gt {a b : Nat} (h : b < a) : compare a b = .gt := Nat.compare_eq_gt.mpr h
theorem compare_of_eq {a b : Nat} (h : a = b) : compare a b = .eq := Nat.compare_eq_eq.mpr h

/-- Multiplying both sides by the same positive number keeps the
    comparison. -/
theorem compare_mul_right (a b c : Nat) (hc : 0 < c) :
    compare (a * c) (b * c) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [compare_of_lt h, compare_of_lt (Nat.mul_lt_mul_of_pos_right h hc)]
  · rw [h, compare_of_eq rfl, compare_of_eq rfl]
  · rw [compare_of_gt h, compare_of_gt (Nat.mul_lt_mul_of_pos_right h hc)]

/-- Comparing whole numbers as integers is comparing them as
    naturals. -/
theorem compare_natCast (a b : Nat) : compare (a : Int) (b : Int) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [compare_of_lt h, Int.compare_eq_lt.mpr (by omega)]
  · rw [h, compare_of_eq rfl, Int.compare_eq_eq.mpr rfl]
  · rw [compare_of_gt h, Int.compare_eq_gt.mpr (by omega)]

/-- Comparing two negated whole numbers swaps the comparison. -/
theorem compare_neg_natCast (a b : Nat) :
    compare (-(a : Int)) (-(b : Int)) = compare b a := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [compare_of_gt h, Int.compare_eq_gt.mpr (by omega)]
  · rw [h, compare_of_eq rfl, Int.compare_eq_eq.mpr rfl]
  · rw [compare_of_lt h, Int.compare_eq_lt.mpr (by omega)]

/-! ## Digit counts -/

theorem pow10_pos (k : Nat) : 0 < 10 ^ k := Nat.pow_pos_iff.mpr (Or.inl (by decide))

theorem numDigits_pos (n : Nat) : 1 ≤ numDigits n := by
  rw [numDigits.eq_1]; split <;> omega

theorem lt_pow_numDigits (n : Nat) : n < 10 ^ numDigits n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [numDigits.eq_1]
    split
    · rename_i h; rw [Nat.pow_one]; exact h
    · have := ih (n / 10) (by omega)
      rw [Nat.pow_add, Nat.pow_one]
      omega

theorem pow_numDigits_le (n : Nat) (hn : 1 ≤ n) : 10 ^ (numDigits n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [numDigits.eq_1]
    split
    · simpa using hn
    · rename_i h
      have h1 := ih (n / 10) (by omega) (by omega)
      have h2 := numDigits_pos (n / 10)
      have : 1 + numDigits (n / 10) - 1 = (numDigits (n / 10) - 1) + 1 := by omega
      rw [this, Nat.pow_succ]
      omega

/-! ## The magnitude comparison -/

/-- The value of a nonzero significand times `10^k` lies in
    `[10^(d-1+k), 10^(d+k))`, where `d` is its digit count. -/
theorem mag_bounds (s k : Nat) (hs : s ≠ 0) :
    10 ^ (numDigits s - 1 + k) ≤ s * 10 ^ k ∧ s * 10 ^ k < 10 ^ (numDigits s + k) := by
  have h1 := pow_numDigits_le s (by omega)
  have h2 := lt_pow_numDigits s
  have hp : 0 < 10 ^ k := pow10_pos k
  refine ⟨?_, ?_⟩
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 hp

/-- `magCmp` compares the magnitudes exactly: for a base `m` at most
    both exponents, as the significands scaled up to `10^m`. -/
theorem magCmp_eq (a b : NumVal) (m : Int) (ha : m ≤ a.exp) (hb : m ≤ b.exp)
    (hA : a.sig ≠ 0) (hB : b.sig ≠ 0) :
    magCmp a b = compare (a.sig * 10 ^ (a.exp - m).toNat) (b.sig * 10 ^ (b.exp - m).toNat) := by
  obtain ⟨an, A, ea⟩ := a
  obtain ⟨bn, B, eb⟩ := b
  dsimp only at *
  have hka : (((ea - m).toNat : Nat) : Int) = ea - m := Int.toNat_of_nonneg (by omega)
  have hkb : (((eb - m).toNat : Nat) : Int) = eb - m := Int.toNat_of_nonneg (by omega)
  generalize (ea - m).toNat = ka at hka ⊢
  generalize (eb - m).toNat = kb at hkb ⊢
  obtain ⟨la, ua⟩ := mag_bounds A ka hA
  obtain ⟨lb, ub⟩ := mag_bounds B kb hB
  have pa := numDigits_pos A
  have pb := numDigits_pos B
  unfold magCmp
  dsimp only
  generalize numDigits A = na at *
  generalize numDigits B = nb at *
  by_cases h1 : (na : Int) + ea < (nb : Int) + eb
  · rw [ite_eq_left h1]
    have hle : na + ka ≤ nb - 1 + kb := by omega
    have := Nat.pow_le_pow_right (by decide : 0 < 10) hle
    exact (compare_of_lt (by omega)).symm
  · rw [ite_eq_right h1]
    by_cases h2 : (na : Int) + ea > (nb : Int) + eb
    · rw [ite_eq_left h2]
      have hle : nb + kb ≤ na - 1 + ka := by omega
      have := Nat.pow_le_pow_right (by decide : 0 < 10) hle
      exact (compare_of_gt (by omega)).symm
    · rw [ite_eq_right h2]
      have hp : 0 < 10 ^ ka := pow10_pos ka
      have hq : 0 < 10 ^ kb := pow10_pos kb
      by_cases h3 : nb ≤ na
      · rw [ite_eq_left h3]
        have hk : kb = (na - nb) + ka := by omega
        rw [hk, Nat.pow_add, ← Nat.mul_assoc, compare_mul_right _ _ _ hp]
      · rw [ite_eq_right h3]
        have hk : ka = (nb - na) + kb := by omega
        rw [hk, Nat.pow_add, ← Nat.mul_assoc, compare_mul_right _ _ _ hq]

/-- `NumVal.cmp` compares exact values: over any base `10^m` with
    `m` at most both exponents, as the signed whole numbers. -/
theorem cmp_exact (a b : NumVal) (m : Int) (ha : m ≤ a.exp) (hb : m ≤ b.exp) :
    NumVal.cmp a b = compare (atBase a.neg a.sig a.exp m) (atBase b.neg b.sig b.exp m) := by
  have hmag := fun hA hB => magCmp_eq a b m ha hb hA hB
  have hmag' := fun hB hA => magCmp_eq b a m hb ha hB hA
  obtain ⟨an, A, ea⟩ := a
  obtain ⟨bn, B, eb⟩ := b
  dsimp only at *
  unfold NumVal.cmp atBase
  dsimp only
  have hpa : 0 < 10 ^ (ea - m).toNat := pow10_pos _
  have hpb : 0 < 10 ^ (eb - m).toNat := pow10_pos _
  generalize hX : A * 10 ^ (ea - m).toNat = X at *
  generalize hY : B * 10 ^ (eb - m).toNat = Y at *
  have hX0 : A = 0 → X = 0 := fun h => by rw [← hX, h, Nat.zero_mul]
  have hXp : A ≠ 0 → 0 < X := fun h => by rw [← hX]; exact Nat.mul_pos (by omega) hpa
  have hY0 : B = 0 → Y = 0 := fun h => by rw [← hY, h, Nat.zero_mul]
  have hYp : B ≠ 0 → 0 < Y := fun h => by rw [← hY]; exact Nat.mul_pos (by omega) hpb
  by_cases hA : A = 0 <;> by_cases hB : B = 0
  · rw [hX0 hA, hY0 hB]; cases an <;> cases bn <;> simp [hA, hB]
  · have := hYp hB; rw [hX0 hA]
    cases an <;> cases bn <;> simp [hA, hB] <;>
      first
      | exact (Int.compare_eq_gt.mpr (by omega)).symm
      | exact (Int.compare_eq_lt.mpr (by omega)).symm
  · have := hXp hA; rw [hY0 hB]
    cases an <;> cases bn <;> simp [hA, hB] <;>
      first
      | exact (Int.compare_eq_gt.mpr (by omega)).symm
      | exact (Int.compare_eq_lt.mpr (by omega)).symm
  · have := hXp hA; have := hYp hB
    cases an <;> cases bn <;> simp [hA, hB]
    · rw [hmag hA hB, compare_natCast]
    · exact (Int.compare_eq_gt.mpr (by omega)).symm
    · exact (Int.compare_eq_lt.mpr (by omega)).symm
    · rw [hmag' hB hA]
      exact (compare_neg_natCast X Y).symm

/-! ## Digit runs -/

/-- The checker's left fold over digits is the positional value. -/
theorem foldl_digits (acc : Nat) (ds : List Char) :
    ds.foldl (fun a c => a * 10 + (c.toNat - 48)) acc = acc * 10 ^ ds.length + digitsValue ds := by
  induction ds generalizing acc with
  | nil => simp [digitsValue]
  | cons c cs ih =>
    rw [List.foldl_cons, ih, digitsValue, List.length_cons, Nat.pow_succ]
    have h0 : '0'.toNat = 48 := rfl
    rw [h0, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ cs.length), Nat.add_assoc]

theorem digitsVal_eq (ds : List Char) : digitsVal ds = digitsValue ds := by
  unfold digitsVal; rw [foldl_digits]; simp

theorem isDigit_of_IsDigit {c : Char} (h : Json.IsDigit c) : c.isDigit = true := by
  obtain ⟨h1, h2⟩ := h
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

/-- `span` over a run of characters that pass, followed by a list
    that is empty or starts with one that fails. -/
theorem span_loop_append (p : Char → Bool) (xs ys acc : List Char)
    (hx : ∀ x ∈ xs, p x = true) (hy : ∀ y r, ys = y :: r → p y = false) :
    List.span.loop p (xs ++ ys) acc = (acc.reverse ++ xs, ys) := by
  induction xs generalizing acc with
  | nil =>
    cases ys with
    | nil => simp [List.span.loop]
    | cons y r => simp [List.span.loop, hy y r rfl]
  | cons x xs ih =>
    rw [List.cons_append, List.span.loop, hx x List.mem_cons_self]
    dsimp only
    rw [ih _ (fun z hz => hx z (List.mem_cons_of_mem _ hz))]
    simp

theorem span_append (p : Char → Bool) (xs ys : List Char)
    (hx : ∀ x ∈ xs, p x = true) (hy : ∀ y r, ys = y :: r → p y = false) :
    (xs ++ ys).span p = (xs, ys) := by
  unfold List.span
  rw [span_loop_append p xs ys [] hx hy]
  simp

/-! ## Normal form -/

/-- Dividing out a factor of ten and raising the exponent keeps the
    value over any base. -/
theorem strip_value (neg : Bool) : ∀ (fuel s : Nat) (e m : Int), m ≤ e →
    (strip neg fuel s e).neg = neg ∧ e ≤ (strip neg fuel s e).exp ∧
      atBase neg (strip neg fuel s e).sig (strip neg fuel s e).exp m = atBase neg s e m
  | 0, s, e, m, _ => by simp [strip]
  | fuel + 1, s, e, m, hm => by
    rw [strip]
    split
    · rename_i h
      obtain ⟨h1, h2, h3⟩ := strip_value neg fuel (s / 10) (e + 1) m (by omega)
      refine ⟨h1, by omega, ?_⟩
      rw [h3]
      unfold atBase
      have hk : (e + 1 - m).toNat = (e - m).toNat + 1 := by omega
      rw [hk, Nat.pow_succ, Nat.mul_comm (10 ^ (e - m).toNat) 10, ← Nat.mul_assoc,
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1)]
    · exact ⟨rfl, Int.le_refl _, rfl⟩

/-- The normal form has the value it was built from. Its exponent is
    at least the one given, unless the value is zero. -/
theorem mkNumVal_value (neg : Bool) (s : Nat) (e m : Int) (hm : m ≤ e) :
    (s = 0 ∨ e ≤ (mkNumVal neg s e).exp) ∧
      atBase (mkNumVal neg s e).neg (mkNumVal neg s e).sig (mkNumVal neg s e).exp m =
        atBase neg s e m := by
  unfold mkNumVal
  split
  · rename_i h; subst h; simp [atBase]
  · obtain ⟨h1, h2, h3⟩ := strip_value neg s s e m hm
    rw [h1]
    exact ⟨Or.inr h2, h3⟩

theorem mkNumVal_exp (neg : Bool) (s : Nat) (e : Int) : min 0 e ≤ (mkNumVal neg s e).exp := by
  unfold mkNumVal
  split
  · simp; omega
  · have := (strip_value neg s s e e (Int.le_refl _)).2.1; omega

/-! ## Reading a number text -/

/-- A digit is none of the characters the number grammar puts
    around digit runs. -/
theorem ne_of_dig {c : Char} (h : Json.IsDigit c) : c ≠ '-' ∧ c ≠ '+' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact Json.Proofs.IsDigit.ne_of_toNat h (by decide)

/-- `span` takes a whole run of digits. -/
theorem span_digits (d : Char) (ds : List Char) (hd : Json.IsDigit d) (hds : ∀ x ∈ ds, Json.IsDigit x) :
    (d :: ds).span (·.isDigit) = (d :: ds, []) := by
  have := span_append (·.isDigit) (d :: ds) [] (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact isDigit_of_IsDigit hd
    · exact isDigit_of_IsDigit (hds x hx)) (by simp)
  simpa using this

/-- An unsigned exponent denotes its digits' value. -/
theorem expValue_plain (ec d : Char) (ds : List Char) (n1 : d ≠ '-') (n2 : d ≠ '+') :
    expValue (ec :: d :: ds) = (digitsValue (d :: ds) : Int) := by
  unfold expValue
  split
  · rename_i heq; simp at heq
  · rename_i heq; simp at heq; exact absurd heq.2.1 n1
  · rename_i heq; simp at heq; exact absurd heq.2.1 n2
  · rename_i heq; simp at heq; rw [heq.2]

/-- `numVal`'s exponent step on an exponent part of the grammar. -/
theorem withExp_eq (neg : Bool) (ids fds : List Char) (ec : Char) (sgn : List Char) (d : Char)
    (ds : List Char) (hs : sgn = [] ∨ sgn = ['-'] ∨ sgn = ['+'])
    (hd : Json.IsDigit d) (hds : ∀ x ∈ ds, Json.IsDigit x) :
    numVal.withExp neg ids fds (sgn ++ d :: ds) =
      some (mkNumVal neg (digitsVal (ids ++ fds)) (expValue (ec :: (sgn ++ d :: ds)) - fds.length)) := by
  obtain ⟨n1, n2, -, -, -⟩ := ne_of_dig hd
  have hsp := span_digits d ds hd hds
  unfold numVal.withExp
  split
  rename_i heq
  rcases hs with rfl | rfl | rfl
  · split at heq
    · rename_i hc; simp at hc; exact absurd hc.1 n1
    · rename_i hc; simp at hc; exact absurd hc.1 n2
    · simp only [List.nil_append, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hsp]
      simp [expValue_plain ec d ds n1 n2, digitsVal_eq]
  · split at heq
    · rename_i hc; simp at hc
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [← hc, hsp]
      simp [expValue, digitsVal_eq]
    · rename_i hc; simp at hc
    · rename_i hc1 _; exact absurd (hc1 (d :: ds) rfl) (by simp)
  · split at heq
    · rename_i hc; simp at hc
    · rename_i hc; simp at hc
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [← hc, hsp]
      simp [expValue, digitsVal_eq]
    · rename_i _ hc2; exact absurd (hc2 (d :: ds) rfl) (by simp)

/-- `numVal`'s last step on an exponent part of the grammar, or none. -/
theorem finish_eq (neg : Bool) (ids fds ex : List Char) (hx : Json.ExpOk ex) :
    numVal.finish neg ids fds ex =
      some (mkNumVal neg (digitsVal (ids ++ fds)) (expValue ex - fds.length)) := by
  rcases hx with rfl | ⟨ec, sgn, d, ds, rfl, hec, hs, hd, hds⟩
  · simp [numVal.finish, expValue]
  · rcases hec with rfl | rfl
    · rw [numVal.finish]; exact withExp_eq neg ids fds 'e' sgn d ds hs hd hds
    · rw [numVal.finish]; exact withExp_eq neg ids fds 'E' sgn d ds hs hd hds

/-- What may follow a run of digits: nothing, or an exponent letter. -/
theorem expOk_head {ex : List Char} (hx : Json.ExpOk ex) :
    ∀ y r, ex = y :: r → y.isDigit = false ∧ y ≠ '.' := by
  intro y r h
  rcases hx with rfl | ⟨ec, sgn, d, ds, rfl, hec, -, -, -⟩
  · cases h
  · simp only [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases hec with rfl | rfl <;> decide

/-- `numVal` on a number text of the grammar: the normal form of its
    sign, its digits, and its exponent less the fraction length. -/
theorem numVal_numberText (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    numVal (numberText neg ints frac ex) =
      some (mkNumVal neg (digitsVal (ints ++ frac)) (expValue ex - frac.length)) := by
  obtain ⟨i, is, rfl⟩ : ∃ i is, ints = i :: is := by
    cases ints with
    | nil => exact absurd rfl hi.1
    | cons i is => exact ⟨i, is, rfl⟩
  have hdig : ∀ x ∈ i :: is, x.isDigit = true := fun x hx => isDigit_of_IsDigit (hi.2 x hx)
  have hfdig : ∀ x ∈ frac, x.isDigit = true := fun x hx => isDigit_of_IsDigit (hf x hx)
  obtain ⟨ni, -, -, -, -⟩ := ne_of_dig (hi.2 i List.mem_cons_self)
  have hfin := finish_eq neg (i :: is) frac ex hx
  have hfin0 := finish_eq neg (i :: is) [] ex hx
  have hxh := expOk_head hx
  -- the text after the integer digits
  have hspan1 : ((i :: is) ++ ((if frac = [] then [] else '.' :: frac) ++ ex)).span (·.isDigit) =
      (i :: is, (if frac = [] then [] else '.' :: frac) ++ ex) := by
    apply span_append _ _ _ hdig
    intro y r h
    split at h
    · exact (hxh y r (by simpa using h)).1
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h; decide
  have hspan2 : (frac ++ ex).span (·.isDigit) = (frac, ex) :=
    span_append _ _ _ hfdig (fun y r h => (hxh y r h).1)
  have htext : numberText neg (i :: is) frac ex =
      (if neg then ['-'] else []) ++ ((i :: is) ++ ((if frac = [] then [] else '.' :: frac) ++ ex)) := by
    simp [numberText, List.append_assoc]
  rw [htext]
  generalize hT : (i :: is) ++ ((if frac = [] then [] else '.' :: frac) ++ ex) = T at hspan1
  unfold numVal
  split
  rename_i heq
  split at heq
  · rename_i hc
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    cases neg
    · exfalso; rw [← hT] at hc; simp at hc; exact ni hc.1
    · simp at hc; subst hc
      rw [hspan1]
      dsimp only
      rw [ite_eq_right (by simp)]
      by_cases hfr : frac = []
      · subst hfr
        simp only [ite_true, List.nil_append] at hfin0 ⊢
        split
        · exact absurd rfl (hxh '.' _ rfl).2
        · simpa using hfin0
      · rw [ite_eq_right hfr]
        split
        · rename_i r hc
          simp only [List.cons_append, List.cons.injEq, true_and] at hc
          rw [← hc, hspan2]
          dsimp only
          rw [ite_eq_right (by cases frac with | nil => exact absurd rfl hfr | cons => simp)]
          exact hfin
        · rename_i hc; exact absurd (hc (frac ++ ex) rfl) id
  · rename_i hc
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    cases neg
    · simp only [Bool.false_eq_true, ite_false, List.nil_append]
      rw [hspan1]
      dsimp only
      rw [ite_eq_right (by simp)]
      by_cases hfr : frac = []
      · subst hfr
        simp only [ite_true, List.nil_append] at hfin0 ⊢
        split
        · exact absurd rfl (hxh '.' _ rfl).2
        · simpa using hfin0
      · rw [ite_eq_right hfr]
        split
        · rename_i r hc
          simp only [List.cons_append, List.cons.injEq, true_and] at hc
          rw [← hc, hspan2]
          dsimp only
          rw [ite_eq_right (by cases frac with | nil => exact absurd rfl hfr | cons => simp)]
          exact hfin
        · rename_i hc; exact absurd (hc (frac ++ ex) rfl) id
    · exact absurd (hc T rfl) id

/-- `numVal` reads a number text of the grammar as its exact value. -/
theorem numVal_value (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      ∀ m, m ≤ v.exp → m ≤ expValue ex - frac.length →
        atBase v.neg v.sig v.exp m =
          atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length) m := by
  refine ⟨_, numVal_numberText neg ints frac ex hi hf hx, fun m _ hm => ?_⟩
  rw [(mkNumVal_value _ _ _ m hm).2, digitsVal_eq]

/-- A whole number as a number value has that value. -/
theorem ofInt_value (n m : Int) (hm : m ≤ 0) :
    m ≤ (NumVal.ofInt n).exp ∧
      atBase (NumVal.ofInt n).neg (NumVal.ofInt n).sig (NumVal.ofInt n).exp m =
        n * 10 ^ (-m).toNat := by
  unfold NumVal.ofInt
  refine ⟨by have := mkNumVal_exp (decide (n < 0)) n.natAbs 0; omega, ?_⟩
  rw [(mkNumVal_value _ _ _ m hm).2]
  unfold atBase
  rw [Int.natCast_mul, Int.natCast_pow, show (0 - m).toNat = (-m).toNat by omega,
    ← Int.mul_assoc]
  congr 1
  by_cases h : n < 0
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; omega

/-- The comparison the date rules make: the current time against a
    number text of the grammar is the exact comparison of the whole
    number with the text's decimal value. -/
theorem numVal_cmp_now (now : Int) (neg : Bool) (ints frac ex : List Char)
    (hi : ints ≠ [] ∧ ∀ d ∈ ints, Json.IsDigit d) (hf : ∀ d ∈ frac, Json.IsDigit d)
    (hx : Json.ExpOk ex) :
    ∃ v, numVal (numberText neg ints frac ex) = some v ∧
      NumVal.cmp (NumVal.ofInt now) v =
        compare (now * 10 ^ (-(min 0 (expValue ex - frac.length))).toNat)
          (atBase neg (digitsValue (ints ++ frac)) (expValue ex - frac.length)
            (min 0 (expValue ex - frac.length))) := by
  refine ⟨_, numVal_numberText neg ints frac ex hi hf hx, ?_⟩
  have hv := mkNumVal_exp neg (digitsVal (ints ++ frac)) (expValue ex - frac.length)
  obtain ⟨h1, h2⟩ := ofInt_value now (min 0 (expValue ex - frac.length)) (Int.min_le_left _ _)
  rw [cmp_exact _ _ (min 0 (expValue ex - frac.length)) h1 hv, h2,
    (mkNumVal_value _ _ _ _ (Int.min_le_right _ _)).2, digitsVal_eq]

end Jws.Proofs.Num

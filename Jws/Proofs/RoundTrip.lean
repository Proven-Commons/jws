/-
  The round trip proof: for every well formed value, parsing its
  printed form gives the value back.

  The statement proved here is `parse_print`. A matching statement
  in a spec file still has to be added by a reviewer, so this file
  builds on its own, in the same shape as the codec proofs.

  Helper lemmas live in `Json.Proofs`. The main step is `key`, a
  strong induction on the length of the printed form that proves
  three statements together: one for a value, one for the inside of
  an array, and one for the inside of an object. The array and
  object statements spend the value statement at the same bound,
  and the value statement spends them at a smaller bound, because
  the brackets around a body add two characters to its length.
-/

import Json

namespace Json.Proofs

open Json

set_option maxRecDepth 10000

/-- What may follow a printed number inside a printed array or
    object, or at the end of a text: the next character, if there
    is one, is not a digit, a point, or an exponent letter, so the
    number parser stops at the end of the number. -/
def TailOk (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c →
    isDigit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E'

theorem tailOk_nil : TailOk [] := by
  intro c h
  simp at h

theorem tailOk_comma (rest : List Char) : TailOk (',' :: rest) := by
  intro c h
  simp at h
  subst h
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem tailOk_rbracket (rest : List Char) : TailOk (']' :: rest) := by
  intro c h
  simp at h
  subst h
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem tailOk_rbrace (rest : List Char) : TailOk ('}' :: rest) := by
  intro c h
  simp at h
  subst h
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem char_le_toNat {a b : Char} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le] at h
  exact h

theorem char_le_of_toNat {a b : Char} (h : a.toNat ≤ b.toNat) : a ≤ b := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]
  exact h

/-- The digit range of a character, in code points. -/
theorem isDigit_range {c : Char} (h : IsDigit c) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have h1 : ('0' : Char).toNat ≤ c.toNat := by
    have := h.1
    rwa [Char.le_def] at this
  have h2 : c.toNat ≤ ('9' : Char).toNat := by
    have := h.2
    rwa [Char.le_def] at this
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- A character the grammar treats as a digit passes the digit
    test. -/
theorem isDigit_of_isDigit {c : Char} (h : IsDigit c) : isDigit c = true := by
  show decide ('0' ≤ c ∧ c ≤ '9') = true
  rw [decide_eq_true_eq]
  exact h

/-- A character that passes the digit test is a digit. -/
theorem isDigit_of_test {c : Char} (h : isDigit c = true) : IsDigit c := by
  have h2 : decide ('0' ≤ c ∧ c ≤ '9') = true := h
  rwa [decide_eq_true_eq] at h2

/-- A digit differs from each character with a code point outside
    the digit range. -/
theorem IsDigit.ne_of_toNat {c d : Char} (h : IsDigit c)
    (hd : d.toNat < 48 ∨ 57 < d.toNat) : c ≠ d := by
  intro e
  have h1 := isDigit_range h
  have h2 : c.toNat = d.toNat := by rw [e]
  omega

/-- Whitespace fails on a character that is none of the four
    whitespace characters. -/
theorem isWs_of_ne {c : Char} (h1 : c ≠ ' ') (h2 : c ≠ '\t')
    (h3 : c ≠ '\n') (h4 : c ≠ '\r') : isWs c = false := by
  simp [isWs, h1, h2, h3, h4]

/-- A digit is not whitespace, and is not one of the marks that can
    follow or extend a number. -/
theorem IsDigit.isWs_false {c : Char} (h : IsDigit c) : isWs c = false :=
  isWs_of_ne
    (IsDigit.ne_of_toNat h (by decide))
    (IsDigit.ne_of_toNat h (by decide))
    (IsDigit.ne_of_toNat h (by decide))
    (IsDigit.ne_of_toNat h (by decide))

theorem IsDigit.ne_rbracket {c : Char} (h : IsDigit c) : c ≠ ']' :=
  IsDigit.ne_of_toNat h (by decide)

theorem IsDigit.ne_rbrace {c : Char} (h : IsDigit c) : c ≠ '}' :=
  IsDigit.ne_of_toNat h (by decide)

theorem IsDigit.ne_comma {c : Char} (h : IsDigit c) : c ≠ ',' :=
  IsDigit.ne_of_toNat h (by decide)

/-- The hex digit for a value below 16 reads back as that value. -/
theorem hexVal_hexDigit : ∀ n : Fin 16, hexVal (hexDigit n.val) = some n.val := by
  decide

theorem hexVal_of_hexDigit {n : Nat} (h : n < 16) : hexVal (hexDigit n) = some n :=
  hexVal_hexDigit ⟨n, h⟩

/-- Skipping whitespace over a list whose head is not whitespace
    changes nothing. -/
theorem skipWs_cons {c : Char} {cs : List Char} (h : isWs c = false) :
    skipWs (c :: cs) = c :: cs := by
  simp [skipWs, h]

/-- The same, for a list followed by more text. -/
theorem skipWs_append_of_head {l rest : List Char} {c : Char}
    (h : l.head? = some c) (hw : isWs c = false) :
    skipWs (l ++ rest) = l ++ rest := by
  cases l with
  | nil => simp at h
  | cons d l =>
    simp at h
    subst h
    simp [List.cons_append, skipWs_cons hw]

/-- A run of digits at the head of a text is read whole: when the
    text after the run does not start with a digit, the digit run
    reader stops at the end of the run. -/
theorem takeDigits_append {ds rest : List Char}
    (hd : ∀ d ∈ ds, isDigit d = true)
    (hr : ∀ c, rest.head? = some c → isDigit c = false) :
    takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds generalizing rest with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r =>
      have hc : isDigit c = false := hr c rfl
      simp [takeDigits, hc]
  | cons d ds ih =>
    have hdd : isDigit d = true := hd d (by simp)
    have ih' := ih (fun x hx => hd x (List.mem_cons_of_mem d hx)) hr
    simp [takeDigits, hdd, ih']

/-- The head of a text built from a fraction part, an exponent
    part, and a tail is never a digit. -/
theorem head_not_digit_of_parts {frac exp rest : List Char}
    (hf : FracOk frac) (he : ExpOk exp) (ht : TailOk rest) :
    ∀ c, (frac ++ exp ++ rest).head? = some c → isDigit c = false := by
  obtain rfl | ⟨d, ds, hfr, hd, -⟩ := hf
  · obtain rfl | ⟨ec, sgn, d, ds, hex, hec, -, -, -⟩ := he
    · intro c hc
      exact (ht c hc).1
    · intro c hc
      have hthis : (exp ++ rest).head? = some ec := by
        rw [hex]
        cases sgn <;> simp
      have h1 : (exp ++ rest).head? = some c := by simpa using hc
      rw [hthis] at h1
      have hcc : ec = c := Option.some.inj h1
      subst hcc
      cases hec with
      | inl h => rw [h]; decide
      | inr h => rw [h]; decide
  · intro c hc
    have h1 : (frac ++ exp ++ rest).head? = some '.' := by
      rw [hfr]; simp
    have hcc : c = '.' := by
      rw [h1] at hc
      exact (Option.some.inj hc).symm
    subst hcc
    decide

/-- The head of a text built from an exponent part and a tail is
    never a digit and never a point. -/
theorem head_not_digit_or_dot_of_exp {exp rest : List Char}
    (he : ExpOk exp) (ht : TailOk rest) :
    ∀ c, (exp ++ rest).head? = some c → isDigit c = false ∧ c ≠ '.' := by
  obtain rfl | ⟨ec, sgn, d, ds, hex, hec, -, -, -⟩ := he
  · intro c hc
    exact ⟨(ht c hc).1, (ht c hc).2.1⟩
  · intro c hc
    have h1 : (exp ++ rest).head? = some ec := by
      rw [hex]
      cases sgn <;> simp
    have h2 : (exp ++ rest).head? = some c := by simpa using hc
    rw [h1] at h2
    have hcc : ec = c := Option.some.inj h2
    subst hcc
    cases hec with
    | inl h => rw [h]; exact ⟨by decide, by decide⟩
    | inr h => rw [h]; exact ⟨by decide, by decide⟩

/-- The integer part of a well formed number text is read whole. -/
theorem parseIntPart_append {hd : Char} {intDs tail : List Char}
    (h0 : (hd = '0' ∧ intDs = []) ∨ ('1' ≤ hd ∧ hd ≤ '9'))
    (hds : ∀ d ∈ intDs, IsDigit d)
    (ht : ∀ c, tail.head? = some c → isDigit c = false) :
    parseIntPart ((hd :: intDs) ++ tail) = some (hd :: intDs, tail) := by
  have hdig : ∀ d ∈ intDs, isDigit d = true :=
    fun d hd' => isDigit_of_isDigit (hds d hd')
  cases h0 with
  | inl h =>
    obtain ⟨rfl, rfl⟩ := h
    simp [parseIntPart]
  | inr h =>
    have hne : hd ≠ '0' := by
      intro e
      have h1 : ('1' : Char).val ≤ hd.val := h.1
      rw [e] at h1
      exact (by decide : ¬ ((49 : UInt32) ≤ (48 : UInt32))) h1
    have htk : takeDigits (intDs ++ tail) = (intDs, tail) :=
      takeDigits_append hdig ht
    simp [parseIntPart, hne, h, htk]

/-- The fraction part of a well formed number text is read whole. -/
theorem parseFracOpt_append {frac tail : List Char} (hf : FracOk frac)
    (ht : ∀ c, tail.head? = some c → isDigit c = false ∧ c ≠ '.') :
    parseFracOpt (frac ++ tail) = some (frac, tail) := by
  cases hf with
  | inl h =>
    rw [h]
    simp only [List.nil_append]
    cases tail with
    | nil => simp [parseFracOpt]
    | cons c r =>
      have hc : c ≠ '.' := (ht c rfl).2
      simp [parseFracOpt, hc]
  | inr h =>
    obtain ⟨d, ds, rfl, hd, hds⟩ := h
    have hdig : ∀ x ∈ d :: ds, isDigit x = true :=
      fun x hx => isDigit_of_isDigit (by
        cases hx with
        | head => exact hd
        | tail _ hx => exact hds x hx)
    have ht' : ∀ c, tail.head? = some c → isDigit c = false :=
      fun c hc => (ht c hc).1
    have htk : takeDigits ((d :: ds) ++ tail) = (d :: ds, tail) :=
      takeDigits_append hdig ht'
    simp only [List.cons_append] at htk
    simp [parseFracOpt, htk]

/-- The exponent part of a well formed number text is read
    whole. -/
theorem parseExpOpt_append {exp rest : List Char} (he : ExpOk exp)
    (ht : TailOk rest) :
    parseExpOpt (exp ++ rest) = some (exp, rest) := by
  cases he with
  | inl h =>
    rw [h]
    simp only [List.nil_append]
    cases rest with
    | nil => rfl
    | cons c r =>
      have hc := ht c rfl
      have hne : ¬ (c = 'e' ∨ c = 'E') := by
        intro hp
        cases hp with
        | inl h1 => exact hc.2.2.1 h1
        | inr h2 => exact hc.2.2.2 h2
      simp [parseExpOpt, hne]
  | inr h =>
    obtain ⟨ec, sgn, d, ds, rfl, hec, hsgn, hd, hds⟩ := h
    have hdig : ∀ x ∈ d :: ds, isDigit x = true :=
      fun x hx => isDigit_of_isDigit (by
        cases hx with
        | head => exact hd
        | tail _ hx => exact hds x hx)
    have ht' : ∀ c, rest.head? = some c → isDigit c = false :=
      fun c hc => (ht c hc).1
    have htk : takeDigits ((d :: ds) ++ rest) = (d :: ds, rest) :=
      takeDigits_append hdig ht'
    simp only [List.cons_append] at htk
    have hdp : d ≠ '+' := IsDigit.ne_of_toNat hd (by decide)
    have hdm : d ≠ '-' := IsDigit.ne_of_toNat hd (by decide)
    cases hsgn with
    | inl h =>
      rw [h]
      simp [parseExpOpt, hec, htk, hdp, hdm]
    | inr h =>
      cases h with
      | inl h =>
        rw [h]
        simp [parseExpOpt, hec, htk, hdp, hdm]
      | inr h =>
        rw [h]
        simp [parseExpOpt, hec, htk, hdp, hdm]

/-- A well formed number text at the head of a text is read whole,
    when what follows cannot extend the number. -/
theorem parseNumber_append {cs rest : List Char} (h : WFNum cs)
    (ht : TailOk rest) :
    parseNumber (cs ++ rest) = some (cs, rest) := by
  obtain ⟨neg, hd, intDs, frac, exp, hcs, hhd, hds, hfrac, hexp⟩ := h
  have ht1 : ∀ c, (frac ++ exp ++ rest).head? = some c → isDigit c = false :=
    head_not_digit_of_parts hfrac hexp ht
  have ht2 : ∀ c, (exp ++ rest).head? = some c → isDigit c = false ∧ c ≠ '.' :=
    head_not_digit_or_dot_of_exp hexp ht
  have hint : parseIntPart ((hd :: intDs) ++ (frac ++ exp ++ rest)) =
      some (hd :: intDs, frac ++ exp ++ rest) :=
    parseIntPart_append hhd hds ht1
  have hfrac' : parseFracOpt (frac ++ (exp ++ rest)) = some (frac, exp ++ rest) :=
    parseFracOpt_append hfrac ht2
  have hexp' : parseExpOpt (exp ++ rest) = some (exp, rest) :=
    parseExpOpt_append hexp ht
  have hshape : cs ++ rest =
      (if neg then ['-'] else []) ++ ((hd :: intDs) ++ (frac ++ (exp ++ rest))) := by
    rw [hcs]
    simp [List.append_assoc]
  rw [hshape]
  have hint2 : parseIntPart (hd :: (intDs ++ (frac ++ (exp ++ rest)))) =
      some (hd :: intDs, frac ++ exp ++ rest) := by
    simpa only [List.cons_append, List.append_assoc] using hint
  cases neg with
  | true =>
    simp [parseNumber, hint2, hfrac', hexp', List.append_assoc, List.cons_append, hcs]
  | false =>
    have hne : hd ≠ '-' := by
      cases hhd with
      | inl h => rw [h.1]; decide
      | inr h =>
        have h01 : ('0' : Char).toNat ≤ ('1' : Char).toNat := by decide
        have hdig : IsDigit hd :=
          ⟨char_le_of_toNat (Nat.le_trans h01 (char_le_toNat h.1)), h.2⟩
        exact IsDigit.ne_of_toNat hdig (by decide)
    simp [parseNumber, hne, hint2, hfrac', hexp', List.append_assoc, List.cons_append, hcs]

/-- The hex value of the character `0`. -/
theorem hexVal_zero : hexVal '0' = some 0 := by decide

/-- A list of length under four is not a list of four or more cells.
    Used for the side condition of the parser's short-tail equation. -/
theorem not_four_cons (xs : List Char) (n : Nat) (h : xs.length = n) (hn : n < 4) :
    ∀ (a b cc d : Char) (r : List Char), xs ≠ a :: b :: cc :: d :: r := by
  intro a b cc d r he
  have hl := congrArg List.length he
  simp only [List.length_cons] at hl
  omega

/-- One step of the string body reader at a closing quote. -/
theorem parseStrBody_quote (T : List Char) :
    parseStrBody ('"' :: T) = some ([], T) := by
  cases T with
  | nil =>
    rw [Json.parseStrBody.eq_2]
    simp
  | cons d T =>
    cases T with
    | nil =>
      rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [] 0 rfl (by decide))]
      simp
    | cons e T =>
      cases T with
      | nil =>
        rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e] 1 rfl (by decide))]
        simp
      | cons f T =>
        cases T with
        | nil =>
          rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e, f] 2 rfl (by decide))]
          simp
        | cons g T =>
          cases T with
          | nil =>
            rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e, f, g] 3 rfl (by decide))]
            simp
          | cons h T =>
            rw [Json.parseStrBody.eq_3]
            simp

/-- One step of the string body reader at a raw character. -/
theorem parseStrBody_raw {c : Char} (h1 : c ≠ '"') (h2 : c ≠ '\\')
    (h3 : ¬ c.toNat < 32) (T : List Char) :
    parseStrBody (c :: T) = (parseStrBody T).map (fun (cs, r) => (c :: cs, r)) := by
  cases T with
  | nil =>
    rw [Json.parseStrBody.eq_2]
    simp [h1, h2, h3, Json.parseStrBody.eq_1]
  | cons d T =>
    cases T with
    | nil =>
      rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [] 0 rfl (by decide))]
      simp [h1, h2, h3]
    | cons e T =>
      cases T with
      | nil =>
        rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e] 1 rfl (by decide))]
        simp [h1, h2, h3]
      | cons f T =>
        cases T with
        | nil =>
          rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e, f] 2 rfl (by decide))]
          simp [h1, h2, h3]
        | cons g T =>
          cases T with
          | nil =>
            rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [e, f, g] 3 rfl (by decide))]
            simp [h1, h2, h3]
          | cons h T =>
            rw [Json.parseStrBody.eq_3]
            simp [h1, h2, h3]

/-- One step of the string body reader at a one-letter escape. -/
theorem parseStrBody_escape (e ch : Char) (hne : e ≠ 'u') (hse : simpleEscape e = some ch)
    (T : List Char) :
    parseStrBody ('\\' :: e :: T) =
      (parseStrBody T).map (fun (cs, r) => (ch :: cs, r)) := by
  cases T with
  | nil =>
    rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [] 0 rfl (by decide))]
    simp [hne, hse]
  | cons a T =>
    cases T with
    | nil =>
      rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [a] 1 rfl (by decide))]
      simp [hne, hse]
    | cons b T =>
      cases T with
      | nil =>
        rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [a, b] 2 rfl (by decide))]
        simp [hne, hse]
      | cons cc T =>
        cases T with
        | nil =>
          rw [Json.parseStrBody.eq_4 _ _ _ (not_four_cons [a, b, cc] 3 rfl (by decide))]
          simp [hne, hse]
        | cons d T =>
          rw [Json.parseStrBody.eq_3]
          simp [hne, hse]

/-- One step of the string body reader at a `\uXXXX` escape whose
    value is below the surrogate range. -/
theorem parseStrBody_unicode {a b cc d : Char} {w x y z : Nat}
    (ha : hexVal a = some w) (hb : hexVal b = some x)
    (hc : hexVal cc = some y) (hd : hexVal d = some z)
    (hsmall : w * 4096 + x * 256 + y * 16 + z < 55296) (T : List Char) :
    parseStrBody ('\\' :: 'u' :: a :: b :: cc :: d :: T) =
      (parseStrBody T).map
        (fun (cs, r) => (Char.ofNat (w * 4096 + x * 256 + y * 16 + z) :: cs, r)) := by
  rw [Json.parseStrBody.eq_3]
  simp [ha, hb, hc, hd, hsmall]

/-- Reading back an escaped string body gives the string back:
    the escapes the printer writes are read as the characters
    they stand for, and the closing quote ends the body. -/
theorem parseStrBody_escapeAll (cs : List Char) (rest : List Char) :
    parseStrBody (escapeAll cs ++ '"' :: rest) = some (cs, rest) := by
  induction cs generalizing rest with
  | nil => exact parseStrBody_quote rest
  | cons c cs ih =>
    have hinput : escapeAll (c :: cs) ++ '"' :: rest =
        escape c ++ (escapeAll cs ++ '"' :: rest) := by
      simp [escapeAll, List.append_assoc]
    rw [hinput]
    by_cases h1 : c = '"'
    · subst h1
      show parseStrBody ('\\' :: '"' :: (escapeAll cs ++ '"' :: rest)) =
        some ('"' :: cs, rest)
      rw [parseStrBody_escape '"' '"' (by decide) (by decide) _]
      simp [ih]
    · by_cases h2 : c = '\\'
      · subst h2
        show parseStrBody ('\\' :: '\\' :: (escapeAll cs ++ '"' :: rest)) =
          some ('\\' :: cs, rest)
        rw [parseStrBody_escape '\\' '\\' (by decide) (by decide) _]
        simp [ih]
      · by_cases h3 : c.toNat = 8
        · have hch : Char.ofNat 8 = c := by
            have h4 := Char.ofNat_toNat c
            rw [h3] at h4
            exact h4
          simp only [escape, h1, h2, h3, List.cons_append, List.nil_append, if_true, if_false]
          rw [parseStrBody_escape 'b' (Char.ofNat 8) (by decide) (by decide) _]
          rw [ih, hch]
          rfl
        · by_cases h4 : c.toNat = 9
          · have hch : Char.ofNat 9 = c := by
              have h5 := Char.ofNat_toNat c
              rw [h4] at h5
              exact h5
            simp [escape, h1, h2, h3, h4]
            rw [parseStrBody_escape 't' (Char.ofNat 9) (by decide) (by decide) _]
            rw [ih, hch]
            rfl
          · by_cases h5 : c.toNat = 10
            · have hch : Char.ofNat 10 = c := by
                have h6 := Char.ofNat_toNat c
                rw [h5] at h6
                exact h6
              simp [escape, h1, h2, h3, h4, h5]
              rw [parseStrBody_escape 'n' (Char.ofNat 10) (by decide) (by decide) _]
              rw [ih, hch]
              rfl
            · by_cases h6 : c.toNat = 12
              · have hch : Char.ofNat 12 = c := by
                  have h7 := Char.ofNat_toNat c
                  rw [h6] at h7
                  exact h7
                simp [escape, h1, h2, h3, h4, h5, h6]
                rw [parseStrBody_escape 'f' (Char.ofNat 12) (by decide) (by decide) _]
                rw [ih, hch]
                rfl
              · by_cases h7 : c.toNat = 13
                · have hch : Char.ofNat 13 = c := by
                    have h8 := Char.ofNat_toNat c
                    rw [h7] at h8
                    exact h8
                  simp [escape, h1, h2, h3, h4, h5, h6, h7]
                  rw [parseStrBody_escape 'r' (Char.ofNat 13) (by decide) (by decide) _]
                  rw [ih, hch]
                  rfl
                · by_cases h8 : c.toNat < 32
                  · have hA : hexVal (hexDigit (c.toNat / 16)) = some (c.toNat / 16) :=
                      hexVal_of_hexDigit (by omega)
                    have hB : hexVal (hexDigit (c.toNat % 16)) = some (c.toNat % 16) :=
                      hexVal_of_hexDigit (by omega)
                    have hm : 0 * 4096 + 0 * 256 + (c.toNat / 16) * 16 +
                        (c.toNat % 16) = c.toNat := by omega
                    have hch : Char.ofNat (0 * 4096 + 0 * 256 + (c.toNat / 16) * 16 +
                        (c.toNat % 16)) = c := by
                      rw [hm]
                      exact Char.ofNat_toNat c
                    have hsmall : 0 * 4096 + 0 * 256 + (c.toNat / 16) * 16 +
                        (c.toNat % 16) < 55296 := by omega
                    simp [escape, h1, h2, h3, h4, h5, h6, h7, h8]
                    rw [parseStrBody_unicode hexVal_zero hexVal_zero hA hB hsmall _]
                    rw [ih, hch]
                    rfl
                  · simp [escape, h1, h2, h3, h4, h5, h6, h7, h8]
                    rw [parseStrBody_raw h1 h2 h8 _]
                    simp [ih]

/-! ## Printed forms: lengths and head characters -/

/-- A member of a joined list is no longer than the whole join. -/
theorem mem_join_length {y : List Char} {ys : List (List Char)} (h : y ∈ ys) :
    y.length ≤ (join ys).length := by
  induction ys with
  | nil => simp at h
  | cons z zs ih =>
    cases zs with
    | nil =>
      have hy : y = z := by simpa using h
      simp [join, hy]
    | cons w ws =>
      have hjoin : join (z :: w :: ws) = z ++ ',' :: join (w :: ws) := by simp [join]
      rw [hjoin]
      cases List.mem_cons.mp h with
      | inl h1 =>
        rw [h1]
        simp only [List.length_append, List.length_cons]
        omega
      | inr h2 =>
        have hle := ih h2
        simp only [List.length_append, List.length_cons]
        omega

/-- The printed length of an array is its body length plus the
    two brackets. -/
theorem print_length_arr (vs : List Json) :
    (print (Json.arr vs)).length = (join (vs.map print)).length + 2 := by
  simp [print, List.length_append]

/-- The printed length of an object is its body length plus the
    two braces. -/
theorem print_length_obj (kvs : List (List Char × Json)) :
    (print (Json.obj kvs)).length = (join (kvs.map printPair)).length + 2 := by
  simp [print, List.length_append]

/-- The printed length of one object pair. -/
theorem printPair_length (kv : List Char × Json) :
    (printPair kv).length = (printStr kv.1).length + 1 + (print kv.2).length := by
  cases kv with
  | mk k v =>
    simp only [printPair, List.length_append, List.length_cons]
    omega

/-- The head character of a printed well formed value: never a
    closing bracket, a closing brace, a comma, or whitespace.
    The parser's body readers rely on this. -/
theorem print_head {v : Json} (hv : WF v) :
    ∃ c cs, print v = c :: cs ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' ∧ isWs c = false := by
  cases v with
  | null =>
    exact ⟨'n', ['u', 'l', 'l'], by simp [print], by decide, by decide, by decide,
      by decide⟩
  | bool b =>
    cases b with
    | true =>
      exact ⟨'t', ['r', 'u', 'e'], by simp [print], by decide, by decide, by decide,
        by decide⟩
    | false =>
      exact ⟨'f', ['a', 'l', 's', 'e'], by simp [print], by decide, by decide, by decide,
        by decide⟩
  | str cs =>
    exact ⟨'"', escapeAll cs ++ ['"'], by simp [print, printStr], by decide, by decide,
      by decide, by decide⟩
  | arr vs =>
    exact ⟨'[', join (vs.map print) ++ [']'], by simp [print], by decide, by decide,
      by decide, by decide⟩
  | obj kvs =>
    exact ⟨'{', join (kvs.map printPair) ++ ['}'], by simp [print], by decide, by decide,
      by decide, by decide⟩
  | num cs =>
    have hnum : WFNum cs := by
      cases hv with
      | num h => exact h
    obtain ⟨neg, hd, intDs, frac, exp, hcs, hhd, -, -, -⟩ := hnum
    have hdig : IsDigit hd := by
      cases hhd with
      | inl h => rw [h.1]; exact ⟨by decide, by decide⟩
      | inr h =>
        exact ⟨char_le_of_toNat (Nat.le_trans (by decide) (char_le_toNat h.1)), h.2⟩
    cases neg with
    | true =>
      exact ⟨'-', (hd :: intDs) ++ frac ++ exp, by simp [print, hcs, List.append_assoc],
        by decide, by decide, by decide, by decide⟩
    | false =>
      exact ⟨hd, intDs ++ frac ++ exp, by simp [print, hcs, List.append_assoc],
        IsDigit.ne_of_toNat hdig (by decide), IsDigit.ne_of_toNat hdig (by decide),
        IsDigit.ne_of_toNat hdig (by decide), IsDigit.isWs_false hdig⟩

/-- A printed well formed value has at least one character. -/
theorem print_length_pos {v : Json} (hv : WF v) : 0 < (print v).length := by
  obtain ⟨c, cs, h, -, -, -, -⟩ := print_head hv
  rw [h]
  simp

/-! ## The round trip -/

/-- The three round trip statements at a printed length bound:
    one for a value, one for the inside of an array, and one for
    the inside of an object. -/
def Triple (n : Nat) : Prop :=
  (∀ v, WF v → (print v).length ≤ n → ∀ (f : Nat) (rest : List Char),
    (print v).length + 1 ≤ f → TailOk rest →
    parseValue f (print v ++ rest) = some (v, rest)) ∧
  (∀ vs, (∀ v ∈ vs, WF v) → (join (vs.map print)).length ≤ n →
    ∀ (f : Nat) (rest : List Char), (join (vs.map print)).length + 2 ≤ f →
    parseEls f (join (vs.map print) ++ ']' :: rest) = some (vs, rest)) ∧
  (∀ kvs, (∀ kv ∈ kvs, WF kv.2) → (join (kvs.map printPair)).length ≤ n →
    ∀ (f : Nat) (rest : List Char), (join (kvs.map printPair)).length + 2 ≤ f →
    parseObjEls f (join (kvs.map printPair) ++ '}' :: rest) = some (kvs, rest))

/-- The round trip at any bound, by induction on a larger bound:
    the bounded form of strong induction. The value statement calls
    the two body statements at a smaller bound, spending the two
    enclosing brackets. Each body statement calls the value
    statement at the same bound for its members, and its own tail
    recursion is structural. The fuel each call needs is bounded by
    the printed length, which is what makes the counts line up. -/
theorem key : ∀ n : Nat, Triple n := by
  have aux : ∀ k n, n ≤ k → Triple n := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst hn0
      refine ⟨?_, ?_, ?_⟩
      · intro v hv hlen _ _ _ _
        have hpos := print_length_pos hv
        omega
      · intro vs hvs hlen f rest hf
        cases vs with
        | nil =>
          cases f with
          | zero => omega
          | succ fuel =>
            show parseEls (fuel + 1) (']' :: rest) = some ([], rest)
            rw [Json.parseEls.eq_2]
            have hsk : skipWs (']' :: rest) = ']' :: rest := skipWs_cons (by decide)
            simp [hsk]
        | cons v vs =>
          have hmem : print v ∈ (v :: vs).map print :=
            List.mem_map.mpr ⟨v, List.mem_cons_self, rfl⟩
          have hle := mem_join_length hmem
          have hpos := print_length_pos (hvs v (List.mem_cons_self))
          omega
      · intro kvs hkvs hlen f rest hf
        cases kvs with
        | nil =>
          cases f with
          | zero => omega
          | succ fuel =>
            show parseObjEls (fuel + 1) ('}' :: rest) = some ([], rest)
            rw [Json.parseObjEls.eq_2]
            have hsk : skipWs ('}' :: rest) = '}' :: rest := skipWs_cons (by decide)
            simp [hsk]
        | cons kv kvs =>
          have hmem : printPair kv ∈ (kv :: kvs).map printPair :=
            List.mem_map.mpr ⟨kv, List.mem_cons_self, rfl⟩
          have hle := mem_join_length hmem
          have hpos : 0 < (printPair kv).length := by
            rw [printPair_length]
            omega
          omega
    | succ k ihk =>
      intro n hn
      have ih : ∀ m, m < n → Triple m := fun m hm => ihk m (by omega)
      have hP : ∀ v, WF v → (print v).length ≤ n → ∀ (f : Nat) (rest : List Char),
          (print v).length + 1 ≤ f → TailOk rest →
          parseValue f (print v ++ rest) = some (v, rest) := by
        intro v hv hlen f rest hf htail
        cases f with
        | zero => omega
        | succ fuel =>
          cases v with
          | null => simp [print, Json.parseValue.eq_2, skipWs, isWs]
          | bool b => cases b <;> simp [print, Json.parseValue.eq_2, skipWs, isWs]
          | str cs =>
            have hform : print (Json.str cs) ++ rest =
                '"' :: (escapeAll cs ++ '"' :: rest) := by
              simp [print, printStr, List.append_assoc]
            rw [hform]
            have hsk : skipWs ('"' :: (escapeAll cs ++ '"' :: rest)) =
                '"' :: (escapeAll cs ++ '"' :: rest) := skipWs_cons (by decide)
            simp [Json.parseValue.eq_2, hsk, parseStrBody_escapeAll]
          | num cs =>
            have hnum : WFNum cs := by
              cases hv with
              | num h => exact h
            have hnumc := hnum
            obtain ⟨neg, hd, intDs, frac, exp, hcs, hhd, -, -, -⟩ := hnumc
            have hdig : IsDigit hd := by
              cases hhd with
              | inl h => rw [h.1]; exact ⟨by decide, by decide⟩
              | inr h =>
                exact ⟨char_le_of_toNat (Nat.le_trans (by decide) (char_le_toNat h.1)),
                  h.2⟩
            cases neg with
            | true =>
              have hform : print (Json.num cs) ++ rest =
                '-' :: hd :: (intDs ++ (frac ++ (exp ++ rest))) := by
                simp [print, hcs, List.append_assoc]
              rw [hform]
              have hsk : skipWs ('-' :: hd :: (intDs ++ (frac ++ (exp ++ rest)))) =
                '-' :: hd :: (intDs ++ (frac ++ (exp ++ rest))) :=
                skipWs_cons (by decide)
              have hnumres : parseNumber ('-' :: hd :: (intDs ++ (frac ++ (exp ++ rest)))) =
                some (cs, rest) := by
                have h := parseNumber_append hnum htail
                rwa [show cs ++ rest = '-' :: hd :: (intDs ++ (frac ++ (exp ++ rest))) from
                  by simp [hcs, List.append_assoc]] at h
              simp [Json.parseValue.eq_2, hsk, hnumres]
            | false =>
              have hform : print (Json.num cs) ++ rest =
                hd :: (intDs ++ (frac ++ (exp ++ rest))) := by
                simp [print, hcs, List.append_assoc]
              rw [hform]
              have hsk : skipWs (hd :: (intDs ++ (frac ++ (exp ++ rest)))) =
                hd :: (intDs ++ (frac ++ (exp ++ rest))) :=
                skipWs_cons (IsDigit.isWs_false hdig)
              have hdis : hd = '-' ∨ isDigit hd := Or.inr (isDigit_of_isDigit hdig)
              have hne_q : hd ≠ '"' := IsDigit.ne_of_toNat hdig (by decide)
              have hne_lb : hd ≠ '[' := IsDigit.ne_of_toNat hdig (by decide)
              have hne_lc : hd ≠ '{' := IsDigit.ne_of_toNat hdig (by decide)
              have hne_t : hd ≠ 't' := IsDigit.ne_of_toNat hdig (by decide)
              have hne_f : hd ≠ 'f' := IsDigit.ne_of_toNat hdig (by decide)
              have hne_n : hd ≠ 'n' := IsDigit.ne_of_toNat hdig (by decide)
              have hnumres : parseNumber (hd :: (intDs ++ (frac ++ (exp ++ rest)))) =
                some (cs, rest) := by
                have h := parseNumber_append hnum htail
                rwa [show cs ++ rest = hd :: (intDs ++ (frac ++ (exp ++ rest))) from
                  by simp [hcs, List.append_assoc]] at h
              simp [Json.parseValue.eq_2, hsk, hdis, hnumres, hne_q, hne_lb, hne_lc, hne_t,
                hne_f, hne_n]
          | arr vs =>
            have hvs : ∀ x ∈ vs, WF x := by
              cases hv with
              | arr h => exact h
            have hlenE : (join (vs.map print)).length < n := by
              have h1 : (print (Json.arr vs)).length =
                  (join (vs.map print)).length + 2 := print_length_arr vs
              omega
            have hE := (ih _ hlenE).2.1 vs hvs (Nat.le_refl _) fuel rest (by
              have h1 : (print (Json.arr vs)).length =
                  (join (vs.map print)).length + 2 := print_length_arr vs
              omega)
            have hform : print (Json.arr vs) ++ rest =
                '[' :: (join (vs.map print) ++ ']' :: rest) := by
              simp [print, List.append_assoc]
            rw [hform]
            have hsk : skipWs ('[' :: (join (vs.map print) ++ ']' :: rest)) =
                '[' :: (join (vs.map print) ++ ']' :: rest) := skipWs_cons (by decide)
            simp [Json.parseValue.eq_2, hsk, hE]
          | obj kvs =>
            have hkvs : ∀ kv ∈ kvs, WF kv.2 := by
              cases hv with
              | obj h => exact h
            have hlenO : (join (kvs.map printPair)).length < n := by
              have h1 : (print (Json.obj kvs)).length =
                  (join (kvs.map printPair)).length + 2 := print_length_obj kvs
              omega
            have hO := (ih _ hlenO).2.2 kvs hkvs (Nat.le_refl _) fuel rest (by
              have h1 : (print (Json.obj kvs)).length =
                  (join (kvs.map printPair)).length + 2 := print_length_obj kvs
              omega)
            have hform : print (Json.obj kvs) ++ rest =
                '{' :: (join (kvs.map printPair) ++ '}' :: rest) := by
              simp [print, List.append_assoc]
            rw [hform]
            have hsk : skipWs ('{' :: (join (kvs.map printPair) ++ '}' :: rest)) =
                '{' :: (join (kvs.map printPair) ++ '}' :: rest) := skipWs_cons (by decide)
            simp [Json.parseValue.eq_2, hsk, hO]
      have hE : ∀ vs, (∀ v ∈ vs, WF v) → (join (vs.map print)).length ≤ n →
          ∀ (f : Nat) (rest : List Char), (join (vs.map print)).length + 2 ≤ f →
          parseEls f (join (vs.map print) ++ ']' :: rest) = some (vs, rest) := by
        intro vs
        induction vs with
        | nil =>
          intro _ _ f rest hf
          cases f with
          | zero => omega
          | succ fuel =>
            show parseEls (fuel + 1) (']' :: rest) = some ([], rest)
            rw [Json.parseEls.eq_2]
            have hsk : skipWs (']' :: rest) = ']' :: rest := skipWs_cons (by decide)
            simp [hsk]
        | cons v vs ih =>
          intro hvs hlen f rest hf
          have hv : WF v := hvs v (List.mem_cons_self)
          have hvs' : ∀ x ∈ vs, WF x := fun x hx => hvs x (List.mem_cons_of_mem v hx)
          obtain ⟨c, cs, hprint, hcne1, -, -, hcws⟩ := print_head hv
          have hmemE : print v ∈ (v :: vs).map print :=
            List.mem_map.mpr ⟨v, List.mem_cons_self, rfl⟩
          have hple : (print v).length ≤ n :=
            Nat.le_trans (mem_join_length hmemE) hlen
          cases f with
          | zero => omega
          | succ fuel =>
            cases vs with
            | nil =>
              have hjoin : join ((v :: []).map print) = print v := by simp [join]
              have hPv := hP v hv hple fuel (']' :: rest) (by
                have hmem : print v ∈ (v :: []).map print :=
                  List.mem_map.mpr ⟨v, List.mem_cons_self, rfl⟩
                have hle := mem_join_length hmem
                simp only [List.map_cons, List.map_nil, join] at hf
                omega) (tailOk_rbracket rest)
              rw [hjoin]
              show parseEls (fuel + 1) (print v ++ ']' :: rest) = some (v :: [], rest)
              have hsk1 : skipWs (print v ++ ']' :: rest) = print v ++ ']' :: rest :=
                skipWs_append_of_head (by simp [hprint]) hcws
              have hPv2 : parseValue fuel (c :: (cs ++ ']' :: rest)) =
                  some (v, ']' :: rest) := by
                have e : print v ++ ']' :: rest = c :: (cs ++ ']' :: rest) := by
                  simp [hprint]
                rw [e] at hPv
                exact hPv
              have hsk3 : skipWs (']' :: rest) = ']' :: rest := skipWs_cons (by decide)
              rw [Json.parseEls.eq_2, hsk1, hprint]
              simp [hcne1, hPv2, hsk3]
            | cons w ws =>
              have hjoin : join ((v :: w :: ws).map print) =
                  print v ++ ',' :: join ((w :: ws).map print) := by simp [join]
              have hmono : (join ((w :: ws).map print)).length ≤
                  (join ((v :: w :: ws).map print)).length := by
                rw [hjoin]
                simp only [List.length_append, List.length_cons]
                omega
              have hlen' : (join ((w :: ws).map print)).length ≤ n := Nat.le_trans hmono hlen
              have hf' : (join ((w :: ws).map print)).length + 2 ≤ fuel := by
                have hbl : (join ((v :: w :: ws).map print)).length =
                    (print v).length + 1 + (join ((w :: ws).map print)).length := by
                  rw [hjoin]
                  simp only [List.length_append, List.length_cons]
                  omega
                omega
              have hEls := ih hvs' hlen' fuel rest hf'
              have hPv := hP v hv hple fuel
                ((',' :: join ((w :: ws).map print)) ++ ']' :: rest) (by
                have hmem : print v ∈ (v :: w :: ws).map print :=
                  List.mem_map.mpr ⟨v, List.mem_cons_self, rfl⟩
                have hle := mem_join_length hmem
                omega) (tailOk_comma _)
              have hPvT : parseValue fuel
                  (print v ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest))) =
                  some (v, ',' :: (join ((w :: ws).map print) ++ ']' :: rest)) := hPv
              have hPv2 : parseValue fuel
                  (c :: (cs ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest)))) =
                  some (v, ',' :: (join ((w :: ws).map print) ++ ']' :: rest)) := by
                have e : print v ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest)) =
                    c :: (cs ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest))) := by
                  simp [hprint]
                rw [e] at hPvT
                exact hPvT
              obtain ⟨c2, cs2, hprint2, hc2ne1, -, -, hc2ws⟩ :=
                print_head (hvs' w (List.mem_cons_self))
              have hjoinw : join ((w :: ws).map print) =
                  print w ++ (if ws = [] then [] else ',' :: join (ws.map print)) := by
                cases ws with
                | nil => simp [join]
                | cons x xs => simp [join]
              have hskA : skipWs
                  (c :: (cs ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest)))) =
                  c :: (cs ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest))) :=
                skipWs_cons hcws
              have hskB : skipWs (',' :: (join ((w :: ws).map print) ++ ']' :: rest)) =
                  ',' :: (join ((w :: ws).map print) ++ ']' :: rest) :=
                skipWs_cons (by decide)
              have hsk2 : skipWs (join ((w :: ws).map print) ++ ']' :: rest) =
                  c2 :: (cs2 ++
                    ((if ws = [] then [] else ',' :: join (ws.map print)) ++
                      ']' :: rest)) := by
                have e1 : join ((w :: ws).map print) ++ ']' :: rest =
                    print w ++
                      ((if ws = [] then [] else ',' :: join (ws.map print)) ++
                        ']' :: rest) := by
                  rw [hjoinw, List.append_assoc]
                rw [e1]
                have e2 := skipWs_append_of_head (l := print w)
                  (rest := (if ws = [] then [] else ',' :: join (ws.map print)) ++
                    ']' :: rest) (by simp [hprint2]) hc2ws
                rw [e2, hprint2]
                exact List.cons_append
              rw [hjoin, List.append_assoc, hprint]
              show parseEls (fuel + 1)
                (c :: (cs ++ (',' :: (join ((w :: ws).map print) ++ ']' :: rest)))) =
                some (v :: w :: ws, rest)
              rw [Json.parseEls.eq_2]
              simp only [hskA, hPv2, hskB, hsk2, hEls]
              simp [hcne1, hc2ne1]
      have hO : ∀ kvs, (∀ kv ∈ kvs, WF kv.2) → (join (kvs.map printPair)).length ≤ n →
          ∀ (f : Nat) (rest : List Char), (join (kvs.map printPair)).length + 2 ≤ f →
          parseObjEls f (join (kvs.map printPair) ++ '}' :: rest) = some (kvs, rest) := by
        intro kvs
        induction kvs with
        | nil =>
          intro _ _ f rest hf
          cases f with
          | zero => omega
          | succ fuel =>
            show parseObjEls (fuel + 1) ('}' :: rest) = some ([], rest)
            rw [Json.parseObjEls.eq_2]
            have hsk : skipWs ('}' :: rest) = '}' :: rest := skipWs_cons (by decide)
            simp [hsk]
        | cons kv kvs ih =>
          intro hkvs hlen f rest hf
          cases kv with
          | mk k v =>
            have hv2 : WF v := hkvs (k, v) (List.mem_cons_self)
            have hkvs' : ∀ x ∈ kvs, WF x.2 :=
              fun x hx => hkvs x (List.mem_cons_of_mem (k, v) hx)
            have hpp : printPair (k, v) = '"' :: (escapeAll k ++ '"' :: ':' :: print v) := by
              simp [printPair, printStr, List.append_assoc]
            have hple : (print v).length ≤ n := by
              have h1 : (print v).length ≤ (printPair (k, v)).length := by
                have h := printPair_length (k, v)
                dsimp only at h
                omega
              have hmem : printPair (k, v) ∈ ((k, v) :: kvs).map printPair :=
                List.mem_map.mpr ⟨(k, v), List.mem_cons_self, rfl⟩
              have h2 := mem_join_length hmem
              omega
            cases f with
            | zero => omega
            | succ fuel =>
              cases kvs with
              | nil =>
                have hjoin : join (((k, v) :: []).map printPair) = printPair (k, v) := by
                  simp [join]
                have hPv := hP v hv2 hple fuel ('}' :: rest) (by
                  have h1 : (print v).length ≤ (printPair (k, v)).length := by
                    have h := printPair_length (k, v)
                    dsimp only at h
                    omega
                  have hmem : printPair (k, v) ∈ ((k, v) :: []).map printPair :=
                    List.mem_map.mpr ⟨(k, v), List.mem_cons_self, rfl⟩
                  have h2 := mem_join_length hmem
                  simp only [List.map_cons, List.map_nil, join] at hf
                  omega) (tailOk_rbrace rest)
                rw [hjoin]
                show parseObjEls (fuel + 1) (printPair (k, v) ++ '}' :: rest) =
                  some ((k, v) :: [], rest)
                have hsk1 : skipWs (printPair (k, v) ++ '}' :: rest) =
                    printPair (k, v) ++ '}' :: rest :=
                  skipWs_append_of_head (c := '"') (by simp [hpp]) (by decide)
                have hskC : skipWs (':' :: (print v ++ '}' :: rest)) =
                    ':' :: (print v ++ '}' :: rest) := skipWs_cons (by decide)
                rw [Json.parseObjEls.eq_2]
                simp [hsk1, hpp, parseStrBody_escapeAll, hskC, hPv, skipWs, isWs]
              | cons kv' kvs' =>
                have hjoin : join (((k, v) :: kv' :: kvs').map printPair) =
                    printPair (k, v) ++ ',' :: join ((kv' :: kvs').map printPair) := by
                  simp [join]
                have hmono : (join ((kv' :: kvs').map printPair)).length ≤
                    (join (((k, v) :: kv' :: kvs').map printPair)).length := by
                  rw [hjoin]
                  simp only [List.length_append, List.length_cons]
                  omega
                have hlen' : (join ((kv' :: kvs').map printPair)).length ≤ n :=
                  Nat.le_trans hmono hlen
                have hf' : (join ((kv' :: kvs').map printPair)).length + 2 ≤ fuel := by
                  have hbl : (join (((k, v) :: kv' :: kvs').map printPair)).length =
                      (printPair (k, v)).length + 1 +
                        (join ((kv' :: kvs').map printPair)).length := by
                    rw [hjoin]
                    simp only [List.length_append, List.length_cons]
                    omega
                  omega
                have hO' := ih hkvs' hlen' fuel rest hf'
                have hPv := hP v hv2 hple fuel
                  ((',' :: join ((kv' :: kvs').map printPair)) ++ '}' :: rest) (by
                  have h1 : (print v).length ≤ (printPair (k, v)).length := by
                    have h := printPair_length (k, v)
                    dsimp only at h
                    omega
                  have hmem : printPair (k, v) ∈ ((k, v) :: kv' :: kvs').map printPair :=
                    List.mem_map.mpr ⟨(k, v), List.mem_cons_self, rfl⟩
                  have h2 := mem_join_length hmem
                  omega) (tailOk_comma _)
                cases kv' with
                | mk k' v' =>
                  have hPv2 : parseValue fuel
                      (print v ++
                        (',' :: (join (((k', v') :: kvs').map printPair) ++
                          '}' :: rest))) =
                      some (v, ',' :: (join (((k', v') :: kvs').map printPair) ++
                        '}' :: rest)) := hPv
                  have hskA : skipWs ('"' :: (escapeAll k ++ '"' :: ':' ::
                      (print v ++
                        (',' :: (join (((k', v') :: kvs').map printPair) ++
                          '}' :: rest))))) =
                      '"' :: (escapeAll k ++ '"' :: ':' ::
                        (print v ++
                          (',' :: (join (((k', v') :: kvs').map printPair) ++
                            '}' :: rest)))) :=
                    skipWs_cons (by decide)
                  have hskC2 : skipWs (':' :: (print v ++
                      (',' :: (join (((k', v') :: kvs').map printPair) ++
                        '}' :: rest)))) =
                      ':' :: (print v ++
                        (',' :: (join (((k', v') :: kvs').map printPair) ++
                          '}' :: rest))) :=
                    skipWs_cons (by decide)
                  have hskT2 : skipWs
                      (',' :: (join (((k', v') :: kvs').map printPair) ++
                        '}' :: rest)) =
                      ',' :: (join (((k', v') :: kvs').map printPair) ++
                        '}' :: rest) :=
                    skipWs_cons (by decide)
                  have hpp' : printPair (k', v') =
                      '"' :: (escapeAll k' ++ '"' :: ':' :: print v') := by
                    simp [printPair, printStr, List.append_assoc]
                  have hjoin' : join (((k', v') :: kvs').map printPair) =
                      printPair (k', v') ++
                        (if kvs' = [] then [] else ',' :: join (kvs'.map printPair)) := by
                    cases kvs' with
                    | nil => simp [join]
                    | cons x xs => simp [join]
                  have hsk4 : skipWs (join (((k', v') :: kvs').map printPair) ++
                      '}' :: rest) =
                      '"' :: (escapeAll k' ++ '"' :: (':' :: (print v' ++
                        ((if kvs' = [] then [] else ',' :: join (kvs'.map printPair)) ++
                          '}' :: rest)))) := by
                    have e1 : join (((k', v') :: kvs').map printPair) ++ '}' :: rest =
                        printPair (k', v') ++
                          ((if kvs' = [] then [] else ',' :: join (kvs'.map printPair)) ++
                            '}' :: rest) := by
                      rw [hjoin', List.append_assoc]
                    rw [e1]
                    have e2 := skipWs_append_of_head (l := printPair (k', v')) (c := '"')
                      (rest := (if kvs' = [] then [] else ',' :: join (kvs'.map printPair)) ++
                        '}' :: rest) (by simp [hpp']) (by decide)
                    rw [e2, hpp']
                    simp [List.append_assoc]
                  rw [hjoin, List.append_assoc, hpp]
                  rw [Json.parseObjEls.eq_2]
                  simp only [List.cons_append, List.append_assoc]
                  simp only [hskA, parseStrBody_escapeAll, hskC2, hPv2, hskT2, hsk4, hO']
                  simp
      exact ⟨hP, hE, hO⟩
  intro n
  exact aux n n (Nat.le_refl n)

/-- The round trip: parsing the printed form of a well formed value
    gives the value back. -/
theorem parse_print {v : Json} (hv : WF v) : parse (print v) = some v := by
  have h := (key (print v).length).1 v hv (Nat.le_refl _) ((print v).length + 1) []
    (Nat.le_refl _) tailOk_nil
  have h2 : parseValue ((print v).length + 1) (print v) = some (v, []) := by
    simpa using h
  unfold parse
  simp [h2, skipWs]

end Json.Proofs

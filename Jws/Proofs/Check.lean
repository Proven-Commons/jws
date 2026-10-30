import Jws.Token

/-
  Proofs about the check, `Jws.accept`: what an accepted token is
  known to satisfy, and the lemmas the single token statements in
  `Jws/Spec.lean` use to cover every context at once.
-/

namespace Jws.Proofs

open Jws

/-- `namesUnique` is the test for a list with no name twice. -/
theorem namesUnique_iff (ns : List (List Char)) : namesUnique ns = true ↔ ns.Nodup := by
  induction ns with
  | nil => simp [namesUnique]
  | cons n ns ih =>
    rw [namesUnique, Bool.and_eq_true, ih, List.nodup_cons, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, List.contains_iff_mem]

/-- The shape rules of the check that do not depend on the context:
    the header and the claims are objects, neither repeats a member
    name, and the header has no `crit` member. -/
def shapeOk (t : Token) : Bool :=
  match t.header, t.claims with
  | .obj hkvs, .obj ckvs =>
    namesUnique (hkvs.map Prod.fst) && namesUnique (ckvs.map Prod.fst) &&
      !(hkvs.map Prod.fst).contains "crit".toList
  | _, _ => false

/-- An accepted token passes the shape rules. -/
theorem accept_shape (t : Token) (ctx : Context) (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup ∧
      "crit".toList ∉ hkvs.map Prod.fst := by
  obtain ⟨hd, cl, sig⟩ := t
  unfold accept at h
  split at h
  · cases h
  · split at h
    · rename_i hkvs ckvs hh hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
        List.contains_iff_mem] at h
      exact ⟨hkvs, ckvs, hh, hc, (namesUnique_iff _).mp h.1.1.1,
        (namesUnique_iff _).mp h.1.1.2, h.1.2⟩
    · cases h

/-- An accepted token has a JSON object for its header and for its
    claims, and neither object repeats a member name. -/
theorem accept_names_unique (t : Token) (ctx : Context) (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup := by
  obtain ⟨hkvs, ckvs, hh, hc, n1, n2, _⟩ := accept_shape t ctx h
  exact ⟨hkvs, ckvs, hh, hc, n1, n2⟩

/-- An accepted token's header has no `crit` member. -/
theorem accept_no_crit (t : Token) (ctx : Context) (h : accept t ctx = true) :
    ∃ hkvs, t.header = .obj hkvs ∧ "crit".toList ∉ hkvs.map Prod.fst := by
  obtain ⟨hkvs, _, hh, _, _, _, hcrit⟩ := accept_shape t ctx h
  exact ⟨hkvs, hh, hcrit⟩

/-- A token that fails the shape rules is refused under every
    context. -/
theorem accept_false_of_shape (t : Token) (ctx : Context) (h : shapeOk t = false) :
    accept t ctx = false := by
  cases hp : accept t ctx
  · rfl
  · obtain ⟨hkvs, ckvs, hh, hc, n1, n2, hcrit⟩ := accept_shape t ctx hp
    unfold shapeOk at h
    rw [hh, hc] at h
    dsimp only at h
    rw [(namesUnique_iff _).mpr n1, (namesUnique_iff _).mpr n2] at h
    have : (hkvs.map Prod.fst).contains "crit".toList = false := by
      rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
      exact hcrit
    rw [this] at h
    cases h

/-- A text that parses to a token failing the shape rules: the
    token is there, and every context refuses it. The premise is a
    closed computation, checked in the kernel for each concrete
    text. -/
theorem refused_of_shape (s : List Char) (ctx : Context)
    (h : (match parseToken s with
          | some t => !shapeOk t
          | none => false) = true) :
    ∃ t, parseToken s = some t ∧ accept t ctx = false := by
  cases hp : parseToken s with
  | none => rw [hp] at h; cases h
  | some t =>
    rw [hp] at h
    dsimp only at h
    refine ⟨t, rfl, accept_false_of_shape t ctx ?_⟩
    simpa using h

/-- A pair the lookup finds is a member of the list. -/
theorem mem_of_lookup {β : Type} : ∀ {kvs : List (List Char × β)} {k : List Char} {v : β},
    kvs.lookup k = some v → (k, v) ∈ kvs
  | [], _, _, h => by simp [List.lookup] at h
  | (k', b) :: es, k, v, h => by
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have : (k == k') = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- In a list with no key twice, a member pair is what the lookup
    finds. -/
theorem lookup_of_mem {β : Type} : ∀ {kvs : List (List Char × β)} {k : List Char} {v : β},
    (kvs.map Prod.fst).Nodup → (k, v) ∈ kvs → kvs.lookup k = some v
  | [], _, _, _, hm => by cases hm
  | (k', b) :: es, k, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with he | he
    · cases he
      simp [List.lookup]
    · have hk : k ≠ k' := by
        intro e
        subst e
        exact hnd.1 (List.mem_map.mpr ⟨(k, v), he, rfl⟩)
      have : (k == k') = false := by simpa using hk
      simp only [List.lookup, this]
      exact lookup_of_mem hnd.2 he

/-- The lookup finds something exactly when the key is a member
    name. -/
theorem lookup_isSome_iff {β : Type} : ∀ {kvs : List (List Char × β)} {k : List Char},
    (kvs.lookup k).isSome = true ↔ k ∈ kvs.map Prod.fst
  | [], _ => by simp [List.lookup]
  | (k', b) :: es, k => by
    by_cases hk : k = k'
    · subst hk
      simp [List.lookup]
    · have : (k == k') = false := by simpa using hk
      simp only [List.lookup, this, List.map_cons, List.mem_cons, hk, false_or]
      exact lookup_isSome_iff

/-- The date claim reading of a member the lookup finds. -/
theorem dateClaim_eq {ckvs : List (List Char × Json.Json)} {name : List Char} {v : Json.Json}
    (hl : ckvs.lookup name = some v) :
    dateClaim name (.obj ckvs) = match v with
      | .num cs => (match numVal cs with | some e => .ok e | none => .bad)
      | _ => .bad := by
  simp only [dateClaim, lookup, hl]
  cases v <;> rfl

/-- A date claim that is not `bad` is a number with an exact
    value. -/
theorem dateClaim_num {ckvs : List (List Char × Json.Json)} {name : List Char} {v : Json.Json}
    (hl : ckvs.lookup name = some v) (hb : dateClaim name (.obj ckvs) ≠ .bad) :
    ∃ cs e, v = .num cs ∧ numVal cs = some e ∧ dateClaim name (.obj ckvs) = .ok e := by
  rw [dateClaim_eq hl] at hb ⊢
  cases v with
  | num cs =>
    dsimp only at hb ⊢
    cases hn : numVal cs with
    | none => rw [hn] at hb; exact absurd rfl hb
    | some e => exact ⟨cs, e, rfl, hn, rfl⟩
  | _ => dsimp only at hb; exact absurd rfl hb

/-- What an accepted token satisfies: every rule of the check,
    stated over the members of the header and claims objects. With
    no repeated names, a member pair is the one value of its name.
    The time comparisons are stated with the checker's own exact
    decimal reading (`numVal`) and comparison (`NumVal.cmp`). -/
theorem accept_sound (t : Token) (ctx : Context) (h : accept t ctx = true) :
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
        ∃ vs, ("aud".toList, Json.Json.arr vs) ∈ ckvs ∧ Json.Json.str a ∈ vs) := by
  obtain ⟨hs, ps, hd, cl, sig⟩ := t
  unfold accept at h
  split at h
  · cases h
  · rename_i hnone
    split at h
    · rename_i hkvs ckvs hh hc
      dsimp only at hh hc
      subst hh hc
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hu1, hu2⟩, hcrit⟩, h⟩ := h
      split at h
      · rename_i alg halg
        simp only [Bool.and_eq_true, and_assoc] at h
        obtain ⟨hne, hsig, hallow, hreq, hexp, hnbf, hiat, hiss, haud, hissuer, haudience⟩ := h
        have hnd1 := (namesUnique_iff _).mp hu1
        have hnd2 := (namesUnique_iff _).mp hu2
        -- a date claim that passed is a number with a value
        have date : ∀ (name : List Char) (v : Json.Json),
            (name, v) ∈ ckvs → dateClaim name (.obj ckvs) ≠ .bad →
            ∃ cs e, v = .num cs ∧ numVal cs = some e ∧
              dateClaim name (.obj ckvs) = .ok e := fun name v hm hb =>
          dateClaim_num (lookup_of_mem hnd2 hm) hb
        refine ⟨?_, ?_, hkvs, ckvs, rfl, rfl, hnd1, hnd2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · rw [← List.contains_iff_mem]; exact hnone
        · intro e; subst e; cases hsig
        · rw [← List.contains_iff_mem]; simpa using hcrit
        · refine ⟨alg, mem_of_lookup halg, ?_, List.contains_iff_mem.mp hallow⟩
          simpa using hne
        · intro n hn
          rw [List.all_eq_true] at hreq
          exact lookup_isSome_iff.mp (hreq n hn)
        · intro v hm
          have hb : dateClaim "exp".toList (.obj ckvs) ≠ .bad := by
            intro e; rw [e] at hexp; cases hexp
          obtain ⟨cs, e, hv, hn, hd⟩ := date _ v hm hb
          refine ⟨cs, e, hv, hn, fun now hnow => ?_⟩
          rw [hd, hnow] at hexp
          simpa using hexp
        · intro v hm
          have hb : dateClaim "nbf".toList (.obj ckvs) ≠ .bad := by
            intro e; rw [e] at hnbf; cases hnbf
          obtain ⟨cs, e, hv, hn, hd⟩ := date _ v hm hb
          refine ⟨cs, e, hv, hn, fun now hnow => ?_⟩
          rw [hd, hnow] at hnbf
          simpa using hnbf
        · intro v hm
          have hb : dateClaim "iat".toList (.obj ckvs) ≠ .bad := by
            intro e; rw [e] at hiat; cases hiat
          obtain ⟨cs, e, hv, hn, _⟩ := date _ v hm hb
          exact ⟨cs, e, hv, hn⟩
        · intro v hm
          have hl := lookup_of_mem hnd2 hm
          simp only [issShapeOk, lookup, hl] at hiss
          cases v <;> simp_all
        · intro v hm
          have hl := lookup_of_mem hnd2 hm
          simp only [audShapeOk, lookup, hl] at haud
          cases v with
          | str s => exact Or.inl ⟨s, rfl⟩
          | arr vs =>
            refine Or.inr ⟨vs, rfl, fun x hx => ?_⟩
            rw [List.all_eq_true] at haud
            have := haud x hx
            cases x <;> simp_all
          | _ => cases haud
        · intro i hi
          rw [hi] at hissuer
          dsimp only at hissuer
          split at hissuer
          · rename_i s hl
            have : s = i := by simpa using hissuer
            subst this
            exact mem_of_lookup hl
          · cases hissuer
        · intro hn hm
          rw [hn] at haudience
          dsimp only at haudience
          have := lookup_isSome_iff.mpr hm
          simp only [lookup] at haudience
          rw [Option.isNone_iff_eq_none] at haudience
          rw [haudience] at this
          cases this
        · intro a ha
          rw [ha] at haudience
          dsimp only at haudience
          unfold audOk at haudience
          split at haudience
          · rename_i s hl
            have : s = a := by simpa using haudience
            subst this
            exact Or.inl (mem_of_lookup hl)
          · rename_i vs hl
            refine Or.inr ⟨vs, mem_of_lookup hl, ?_⟩
            rw [List.any_eq_true] at haudience
            obtain ⟨x, hx, hxa⟩ := haudience
            cases x with
            | str s =>
              have : s = a := by simpa using hxa
              subst this
              exact hx
            | _ => cases hxa
          · cases haudience
      · cases h
    · cases h

end Jws.Proofs

import Jws.Token

/-
  Proofs about the check, `Jws.accept`: what an accepted token is
  known to satisfy, and the lemmas the single token statements in
  `Spec.lean` use to cover every context at once.
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

/-- An accepted token has a JSON object for its header and for its
    claims, and neither object repeats a member name. -/
theorem accept_names_unique (t : Token) (ctx : Context) (h : accept t ctx = true) :
    ∃ hkvs ckvs, t.header = .obj hkvs ∧ t.claims = .obj ckvs ∧
      (hkvs.map Prod.fst).Nodup ∧ (ckvs.map Prod.fst).Nodup := by
  obtain ⟨hd, cl, sig⟩ := t
  unfold accept at h
  split at h
  · cases h
  · split at h
    · rename_i hkvs ckvs hh hc
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact ⟨hkvs, ckvs, hh, hc, (namesUnique_iff _).mp h.1.1, (namesUnique_iff _).mp h.1.2⟩
    · cases h

/-- The repeated name test on a token's two objects, as a value:
    true when both parts are objects and neither repeats a name. -/
def namesOk (t : Token) : Bool :=
  match t.header, t.claims with
  | .obj hkvs, .obj ckvs => namesUnique (hkvs.map Prod.fst) && namesUnique (ckvs.map Prod.fst)
  | _, _ => false

/-- A token that fails the repeated name test is refused under
    every context. -/
theorem accept_false_of_names (t : Token) (ctx : Context) (h : namesOk t = false) :
    accept t ctx = false := by
  cases hp : accept t ctx
  · rfl
  · obtain ⟨hkvs, ckvs, hh, hc, n1, n2⟩ := accept_names_unique t ctx hp
    unfold namesOk at h
    rw [hh, hc] at h
    dsimp only at h
    rw [(namesUnique_iff _).mpr n1, (namesUnique_iff _).mpr n2] at h
    cases h

/-- A text that parses to a token failing the repeated name test:
    the token is there, and every context refuses it. The premise
    is a closed computation, checked in the kernel for each
    concrete text. -/
theorem refused_of_names (s : List Char) (ctx : Context)
    (h : (match parseToken s with
          | some t => !namesOk t
          | none => false) = true) :
    ∃ t, parseToken s = some t ∧ accept t ctx = false := by
  cases hp : parseToken s with
  | none => rw [hp] at h; cases h
  | some t =>
    rw [hp] at h
    dsimp only at h
    refine ⟨t, rfl, accept_false_of_names t ctx ?_⟩
    simpa using h

end Jws.Proofs

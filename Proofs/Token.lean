import Jws.Token
import Proofs.RoundTrip
import Proofs.B64
import Proofs.Utf8

namespace Jws.Proofs

open Jws

/-- Splitting reads back a join whose first part is free of the
    separator: the first part comes off whole. -/
theorem splitSep_append (sep : Char) (p rest : List Char) (h : sep ∉ p) :
    splitSep sep (p ++ sep :: rest) = p :: splitSep sep rest := by
  induction p with
  | nil =>
    simp only [List.nil_append]
    rw [splitSep]
    exact if_pos rfl
  | cons c cs ih =>
    have hc : c ≠ sep := by
      intro e
      apply h
      rw [e]
      exact List.mem_cons_self
    have hcs : sep ∉ cs := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.cons_append, splitSep, if_neg hc, ih hcs]

/-- Splitting a text with no separator in it gives the text back
    as the one part. -/
theorem splitSep_of_not_mem (sep : Char) (p : List Char) (h : sep ∉ p) :
    splitSep sep p = [p] := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ sep := by
      intro e
      apply h
      rw [e]
      exact List.mem_cons_self
    have hcs : sep ∉ cs := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [splitSep, if_neg hc, ih hcs]

/-- No character the base64url encoder writes is the dot. -/
theorem encode_ne_dot : ∀ (bs : List UInt8) (c : Char),
    c ∈ Base64url.encode bs → c ≠ '.' := by
  intro bs
  induction bs using Base64url.encode.induct with
  | case1 a b d rest ih =>
    intro c h
    rw [Base64url.encode] at h
    simp only [List.mem_cons] at h
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    have hd := UInt8.toNat_lt d
    rcases h with rfl | rfl | rfl | rfl | h
    · exact Base64url.Proofs.char_ne_dot (by omega)
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · exact ih c h
  | case2 a b =>
    intro c h
    rw [Base64url.encode] at h
    simp only [List.mem_cons, List.mem_singleton] at h
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    rcases h with rfl | rfl | rfl | h
    · exact Base64url.Proofs.char_ne_dot (by omega)
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · cases h
  | case3 a =>
    intro c h
    rw [Base64url.encode] at h
    simp only [List.mem_cons, List.mem_singleton] at h
    have ha := UInt8.toNat_lt a
    rcases h with rfl | rfl | h
    · exact Base64url.Proofs.char_ne_dot (by omega)
    · exact Base64url.Proofs.char_ne_dot (Nat.mod_lt _ (by decide))
    · cases h
  | case4 =>
    intro c h
    cases h

/-- The printed token splits into its three printed parts. -/
theorem splitSep_print (t : Token) :
    splitSep '.' (printToken t) =
      [Base64url.encode (Utf8.encode (Json.print t.header)),
       Base64url.encode (Utf8.encode (Json.print t.claims)),
       Base64url.encode t.sig] := by
  have n1 : ∀ c ∈ Base64url.encode (Utf8.encode (Json.print t.header)), c ≠ '.' :=
    fun c hc => encode_ne_dot _ c hc
  have n2 : ∀ c ∈ Base64url.encode (Utf8.encode (Json.print t.claims)), c ≠ '.' :=
    fun c hc => encode_ne_dot _ c hc
  have n3 : ∀ c ∈ Base64url.encode t.sig, c ≠ '.' :=
    fun c hc => encode_ne_dot _ c hc
  simp only [printToken, joinSep]
  rw [splitSep_append _ _ _ (fun hm => n1 _ hm rfl),
    splitSep_append _ _ _ (fun hm => n2 _ hm rfl),
    splitSep_of_not_mem _ _ (fun hm => n3 _ hm rfl)]

/-- The plan's main claim: parsing a printed token gives the
    token back, for tokens whose JSON parts are well formed in
    the json slice's sense. The proof is a chain of the three
    round trips under it: the JSON text round trip, the UTF-8
    round trip, and the base64url round trip, with the split and
    join of the three parts read back by the two lemmas above. -/
theorem parseToken_print (t : Token) (hh : Json.WF t.header) (hc : Json.WF t.claims) :
    parseToken (printToken t) = some t := by
  obtain ⟨h, c, s⟩ := t
  simp only [parseToken, splitSep_print, Base64url.Proofs.decode_encode,
    Utf8.Proofs.decode_encode, Json.Proofs.parse_print hh, Json.Proofs.parse_print hc]

end Jws.Proofs

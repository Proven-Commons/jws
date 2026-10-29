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

/-- A token made from values prints to the three canonical parts,
    and splits back into them. -/
theorem splitSep_print_make (h c : Json.Json) (sig : List UInt8) :
    splitSep '.' (printToken (makeToken h c sig)) =
      [Base64url.encode (Utf8.encode (Json.print h)),
       Base64url.encode (Utf8.encode (Json.print c)),
       Base64url.encode sig] := by
  have n1 : ∀ x ∈ Base64url.encode (Utf8.encode (Json.print h)), x ≠ '.' :=
    fun x hx => encode_ne_dot _ x hx
  have n2 : ∀ x ∈ Base64url.encode (Utf8.encode (Json.print c)), x ≠ '.' :=
    fun x hx => encode_ne_dot _ x hx
  have n3 : ∀ x ∈ Base64url.encode sig, x ≠ '.' :=
    fun x hx => encode_ne_dot _ x hx
  simp only [printToken, makeToken, joinSep]
  rw [splitSep_append _ _ _ (fun hm => n1 _ hm rfl),
    splitSep_append _ _ _ (fun hm => n2 _ hm rfl),
    splitSep_of_not_mem _ _ (fun hm => n3 _ hm rfl)]

/-- Parsing the printed form of a token made from well formed JSON
    values gives that token back. The proof is a chain of the three
    round trips under it: the JSON text round trip, the UTF-8 round
    trip, and the base64url round trip, with the split and join of
    the three parts read back by the lemmas above. -/
theorem parseToken_print (h c : Json.Json) (sig : List UInt8) (hh : Json.WF h)
    (hc : Json.WF c) :
    parseToken (printToken (makeToken h c sig)) = some (makeToken h c sig) := by
  simp only [parseToken, splitSep_print_make, Base64url.Proofs.decode_encode,
    Utf8.Proofs.decode_encode, Json.Proofs.parse_print hh, Json.Proofs.parse_print hc]
  rfl

/-- Splitting never gives the empty list of parts. -/
theorem splitSep_ne_nil (sep : Char) (cs : List Char) : splitSep sep cs ≠ [] := by
  cases cs with
  | nil => simp [splitSep]
  | cons c rest =>
    rw [splitSep]
    split
    · simp
    · split <;> simp

/-- Joining the parts of a split gives the text back. -/
theorem joinSep_splitSep (sep : Char) : ∀ cs : List Char,
    joinSep sep (splitSep sep cs) = cs
  | [] => rfl
  | c :: rest => by
    have ih := joinSep_splitSep sep rest
    rw [splitSep]
    split
    · rename_i hc
      subst hc
      cases hs : splitSep c rest with
      | nil => exact absurd hs (splitSep_ne_nil _ _)
      | cons q qs =>
        rw [hs] at ih
        rw [joinSep, List.nil_append, ih]
    · split
      · rename_i p ps hs
        rw [hs] at ih
        cases ps with
        | nil => rw [joinSep] at ih ⊢; rw [ih]
        | cons q qs => rw [joinSep] at ih ⊢; rw [List.cons_append, ih]
      · rename_i hs
        rw [hs] at ih
        rw [joinSep]
        rw [joinSep] at ih
        rw [← ih]

/-- What the parser reads: the text splits at its dots into the two
    kept parts and the signature part, which is the base64url form
    of the signature bytes; the header and the claims are what the
    two kept parts decode to, through strict base64url, strict UTF-8
    and the JSON parser. -/
theorem parseToken_reads (s : List Char) (t : Token) (h : parseToken s = some t) :
    splitSep '.' s = [t.headerSeg, t.payloadSeg, Base64url.encode t.sig] ∧
    (∃ hb hcs, Base64url.decode t.headerSeg = some hb ∧ Utf8.decode hb = some hcs ∧
      Json.parse hcs = some t.header) ∧
    (∃ pb pcs, Base64url.decode t.payloadSeg = some pb ∧ Utf8.decode pb = some pcs ∧
      Json.parse pcs = some t.claims) := by
  unfold parseToken at h
  split at h
  · rename_i hs ps ss hsplit
    split at h
    · rename_i hb pb sb e1 e2 e3
      split at h
      · rename_i hcs pcs u1 u2
        split at h
        · rename_i hv pv j1 j2
          cases h
          refine ⟨?_, ⟨hb, hcs, e1, u1, j1⟩, ⟨pb, pcs, e2, u2, j2⟩⟩
          rw [hsplit, Base64url.Proofs.encode_decode _ _ e3]
        · cases h
      · cases h
    · cases h
  · cases h

/-- Printing a parsed token gives the received text back, byte for
    byte: the two kept parts are the received ones, and the
    signature part is the canonical base64url of the signature
    bytes, which the strict decoder only accepts when it is the
    received part. -/
theorem printToken_parse (s : List Char) (t : Token) (h : parseToken s = some t) :
    printToken t = s := by
  have hsplit := (parseToken_reads s t h).1
  rw [printToken, ← hsplit, joinSep_splitSep]

end Jws.Proofs

import PEqualNP.Defs.ProofComplexity

namespace PEqualNP.Research.PHP54Lower

open PEqualNP.ProofComplexity

theorem resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, -, -, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst h
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩

theorem support_bound {V : Type} [DecidableEq V] {F : Set (Clause V)} {π}
    (hd : IsDerivation F π) (S : Finset (Clause V)) (hs : ∀ C ∈ S, C ∈ π) :
    ∃ A : Finset (Clause V), (∀ C ∈ A, C ∈ F) ∧
      (∀ a : V → Bool, (∀ C ∈ A, ClauseSat a C) → ∀ C ∈ S, ClauseSat a C) ∧
      2 * A.card ≤ π.length + S.card := by
  induction hd generalizing S with
  | nil =>
    exact ⟨∅,by simp,by intro a _ C h; exact False.elim (List.not_mem_nil (hs C h)),by simp⟩
  | @ax π c prev ax ih =>
    by_cases hc : c ∈ S
    · obtain ⟨A,hF,ha,hn⟩ := ih (S.erase c) (by
        intro x hx
        exact (List.mem_cons.mp (hs x (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx))
      refine ⟨insert c A,?_,?_,?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ax
        · exact hF x hx
      · intro a h x hx
        by_cases he : x = c
        · subst x; exact h _ (Finset.mem_insert_self ..)
        · exact ha a (fun y hy => h _ (Finset.mem_insert_of_mem hy)) x (Finset.mem_erase.mpr ⟨he,hx⟩)
      · have := Finset.card_insert_le c A
        have := Finset.card_erase_add_one hc
        simp only [List.length_cons]; omega
    · obtain ⟨A,hF,ha,hn⟩ := ih S (by
        intro x hx; exact (List.mem_cons.mp (hs x hx)).resolve_left (fun e => hc (e ▸ hx)))
      exact ⟨A,hF,ha,by simp only [List.length_cons]; omega⟩
  | @res π c d r prev hC hD hR ih =>
    by_cases hr : r ∈ S
    · let T := insert c (insert d (S.erase r))
      obtain ⟨A,hF,ha,hn⟩ := ih T (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hC
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hD
        exact (List.mem_cons.mp (hs x (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx))
      refine ⟨A,hF,?_,?_⟩
      · intro a h x hx
        have ht := ha a h
        by_cases e : x = r
        · subst x
          exact resolvent_sound a hR (ht c (by simp [T])) (ht d (by simp [T]))
        · exact ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hx⟩)))
      · dsimp [T] at hn
        have := Finset.card_insert_le c (insert d (S.erase r))
        have := Finset.card_insert_le d (S.erase r)
        have := Finset.card_erase_add_one hr
        simp only [List.length_cons]; omega
    · obtain ⟨A,hF,ha,hn⟩ := ih S (by
        intro x hx; exact (List.mem_cons.mp (hs x hx)).resolve_left (fun e => hr (e ▸ hx)))
      exact ⟨A,hF,ha,by simp only [List.length_cons]; omega⟩

abbrev Var := Fin 5 × Fin 4
abbrev Cl := Clause Var
def pigeon (i : Fin 5) : Cl := Finset.univ.image (fun j : Fin 4 => ((i,j),true))
def hole (i k : Fin 5) (j : Fin 4) : Cl := {((i,j),false),((k,j),false)}
def clauses : Finset Cl := Finset.univ.image pigeon ∪
  Finset.univ.biUnion fun i : Fin 5 => (Finset.univ.erase i).biUnion fun k : Fin 5 =>
    Finset.univ.image (hole i k)

theorem axiom_mem {c : Cl} (hc : c ∈ PHP 5 4) : c ∈ clauses := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,k,j,hik,rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr
      ⟨k,by simp [Ne.symm hik],Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩

def val (m : Nat) (v : Var) := m.testBit (4 * v.1.val + v.2.val)
def agrees (m : Nat) (c : Cl) := decide (∃ l ∈ c, val m l.1 = l.2)

theorem agrees_iff (m : Nat) (c : Cl) : agrees m c = true ↔ ClauseSat (val m) c := by
  exact decide_eq_true_iff
def keys : List Nat := [541200, 541185, 540705, 525345, 33825, 541201, 540962, 532804, 270728, 540961, 541202, 533524, 272408, 529441, 533522, 541204, 295448, 99361, 164882, 295444, 541208, 540946, 541217, 533569, 272513, 529426, 533537, 541249, 295553, 99346, 164897, 295489, 541313, 528706, 533057, 541729, 296993, 98626, 164417, 295969, 542753, 71746, 141377, 280609, 558113]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem critical : ∀ c ∈ clauses, ∃ m ∈ keys, agrees m c = false ∧
    ∀ d ∈ clauses, d ≠ c → agrees m d = true := by decide

set_option maxRecDepth 6000 in
theorem count : clauses.card = 45 := by decide

theorem length_ge {π : List Cl} (h : IsRefutation (PHP 5 4) π) : 89 ≤ π.length := by
  obtain ⟨A,hF,hd,hn⟩ := support_bound h.1 {∅} (by simpa using h.2)
  have inc : clauses ⊆ A := by
    intro c hc
    by_contra e
    obtain ⟨m,_,_,hm⟩ := critical c hc
    have ha : ∀ x ∈ A, ClauseSat (val m) x := by
      intro x hx
      exact (agrees_iff ..).mp (hm x (axiom_mem (hF x hx)) (fun he => e (he ▸ hx)))
    have := hd (val m) ha ∅ (by simp)
    simp [ClauseSat] at this
  have := Finset.card_le_card inc
  rw [count] at this
  simp only [Finset.card_singleton] at hn
  omega

end PEqualNP.Research.PHP54Lower

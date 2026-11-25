import PEqualNP.Research.L_meta_9822_profiles

namespace PEqualNP.Research.PetersenStars
open PEqualNP.Research.PuncturedPetersen
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def adj (p q : Fin 10) : Bool := edges.contains (min p.val q.val,max p.val q.val)
theorem no_square : ∀ a b c d : Fin 10, a ≠ b → c ≠ d →
  adj a c = true → adj a d = true → adj b c = true → adj b d = false := by decide +kernel

theorem rectangle_is_star (A B : Finset (Fin 10)) (sound : ∀ a ∈ A, ∀ b ∈ B, adj a b = true) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! h
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨c,hc,d,hd,cd⟩ := Finset.one_lt_card.mp h.2
  have off := no_square a b c d ab cd (sound _ ha _ hc) (sound _ ha _ hd) (sound _ hb _ hc)
  rw [sound _ hb _ hd] at off; contradiction

def hits (C : Finset (Fin 10)) := ∀ a b, adj a b = true → a ∈ C ∨ b ∈ C
theorem cover_lower (C : Finset (Fin 10)) (h : hits C) : 6 ≤ C.card := by
  have z : ∀ C : Finset (Fin 10), (∀ a b, adj a b = true → a ∈ C ∨ b ∈ C) → 6 ≤ C.card := by decide +kernel
  exact z C h

/-- Even repeated stars and duplicate edge coverage cannot reduce the leaf count.
Each list element pairs one center with all the leaves of that star. -/
def W := Fin 10 × List (Fin 10)
def cells (s : W) := s.2.map fun v => (min s.1.val v.val,max s.1.val v.val)
def leaves (stars : List W) : Nat := (stars.map fun s => 1+s.2.length).sum

theorem arbitrary_cover (stars : List W) (covers : ∀ e ∈ edges, e ∈ stars.flatMap cells) :
    19 ≤ leaves stars := by
  let C := (stars.map Prod.fst).toFinset
  have hh : hits C := by
    intro a b hit
    obtain ⟨s,hs,hm⟩ := List.mem_flatMap.mp (covers _ (by simpa [adj] using hit))
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp hm
    have ca : s.1 = a ∨ s.1 = b := by
      have e1 := congrArg Prod.fst eq; have e2 := congrArg Prod.snd eq
      simp only at e1 e2
      rcases le_total s.1.val v.val with h | h <;> rcases le_total a.val b.val with k | k <;>
        simp [min_eq_left,min_eq_right,max_eq_left,max_eq_right,h,k] at e1 e2 <;>
        first | exact Or.inl (Fin.ext (by omega)) | exact Or.inr (Fin.ext (by omega))
    have inn : s.1 ∈ C := by simpa [C] using (List.mem_map.mpr ⟨s,hs,rfl⟩ : s.1 ∈ stars.map Prod.fst)
    rcases ca with rfl | rfl <;> simp [inn]
  have l : C.card ≤ stars.length := by
    calc C.card ≤ (stars.map (fun s : W => s.1)).length := List.toFinset_card_le _
         _ = stars.length := List.length_map _
  have e : 13 ≤ (stars.flatMap cells).length := by
    have inc : edges.toFinset ⊆ (stars.flatMap cells).toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (covers x (List.mem_toFinset.mp hx))
    have sz : edges.toFinset.card = 13 := by decide +kernel
    exact sz ▸ (Finset.card_le_card inc).trans (List.toFinset_card_le _)
  have split : leaves stars = stars.length + (stars.flatMap cells).length := by
    induction stars with
    | nil => rfl
    | cons s ss ih => simp [leaves,cells,List.flatMap_cons] at ih ⊢; omega
  have := cover_lower _ hh
  omega
end PEqualNP.Research.PetersenStars

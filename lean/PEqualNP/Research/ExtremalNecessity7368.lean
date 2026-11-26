import PEqualNP.Defs

namespace PEqualNP.Research.Extremal7368

variable {n : ℕ}
abbrev Mask (n : ℕ) := Finset (Fin n)
def Up (W : Set (Mask n)) := ∀ ⦃a b⦄, a ∈ W → a ⊆ b → b ∈ W
def Fits (W : Set (Mask n)) (P N : Mask n → Prop) :=
  (∀ a, P a → a ∈ W) ∧ (∀ a, N a → a ∉ W)
def Compatible (P N : Mask n → Prop) :=
  ∀ p, P p → ∀ q, N q → ¬ p ⊆ q

theorem compatible_of_fits {P N : Mask n → Prop} {W : Set (Mask n)}
    (hu : Up W) (hf : Fits W P N) : Compatible P N := by
  intro p hp q hq sub
  exact hf.2 q hq (hu (hf.1 p hp) sub)

theorem necessary_positive {P N : Mask n → Prop} (hc : Compatible P N)
    {a : Mask n} (ha : P a) (hm : ∀ b, b ⊂ a → ¬ P b) :
    ∃ W V : Set (Mask n), Up W ∧ Up V ∧ Fits W P N ∧
      Fits V (fun b => P b ∧ b ≠ a) N ∧ a ∈ W ∧ a ∉ V ∧
      ∀ b, b ≠ a → (b ∈ W ↔ b ∈ V) := by
  let W : Set (Mask n) := {b | ∃ p, P p ∧ p ⊆ b}
  let V : Set (Mask n) := {b | b ∈ W ∧ b ≠ a}
  have up : Up W := by
    rintro b c ⟨p,hp,sub⟩ h
    exact ⟨p,hp,sub.trans h⟩
  have fits : Fits W P N := by
    refine ⟨fun b hb => ⟨b,hb,Finset.Subset.rfl⟩,?_⟩
    rintro b hb ⟨p,hp,sub⟩
    exact hc p hp b hb sub
  refine ⟨W,V,up,?_,fits,?_,fits.1 a ha,fun h => h.2 rfl,?_⟩
  · rintro b c ⟨wb,d⟩ sub
    refine ⟨up wb sub,?_⟩
    rintro rfl
    obtain ⟨p,hp,hpb⟩ := wb
    exact hm p (lt_of_le_of_lt hpb (lt_of_le_of_ne sub d)) hp
  · exact ⟨fun b h => ⟨fits.1 b h.1,h.2⟩,fun b hb h => fits.2 b hb h.1⟩
  · exact fun b d => ⟨fun h => ⟨h,d⟩,fun h => h.1⟩

theorem necessary_negative {P N : Mask n → Prop} (hc : Compatible P N)
    {a : Mask n} (ha : N a) (hm : ∀ b, a ⊂ b → ¬ N b) :
    ∃ W V : Set (Mask n), Up W ∧ Up V ∧ Fits W P N ∧
      Fits V P (fun b => N b ∧ b ≠ a) ∧ a ∉ W ∧ a ∈ V ∧
      ∀ b, b ≠ a → (b ∈ W ↔ b ∈ V) := by
  let W : Set (Mask n) := {b | ∀ q, N q → ¬ b ⊆ q}
  let V : Set (Mask n) := {b | b ∈ W ∨ b = a}
  have up : Up W := by
    intro b c h sub q hq cq
    exact h q hq (sub.trans cq)
  have fits : Fits W P N := ⟨hc,fun b hb h => h b hb Finset.Subset.rfl⟩
  refine ⟨W,V,up,?_,fits,?_,fits.2 a ha,Or.inr rfl,?_⟩
  · rintro b c (h|rfl) sub
    · exact Or.inl (up h sub)
    · by_cases e : b = c
      · exact Or.inr e.symm
      · left
        intro q hq cq
        exact hm q (lt_of_lt_of_le (lt_of_le_of_ne sub e) cq) hq
  · exact ⟨fun b h => Or.inl (fits.1 b h),fun b hb h => h.elim (fits.2 b hb.1) hb.2⟩
  · exact fun b d => ⟨Or.inl,fun h => h.elim id (fun e => (d e).elim)⟩

#print axioms compatible_of_fits
#print axioms necessary_positive
#print axioms necessary_negative
end PEqualNP.Research.Extremal7368

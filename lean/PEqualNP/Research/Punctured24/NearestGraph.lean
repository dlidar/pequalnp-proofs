import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace PEqualNP.Research.NearestGraph
variable {E X : Type} [DecidableEq E] [Fintype X]
/-- For graph functions, `hit e x` says both endpoints of edge e are on. -/
def accepts (hit : E → X → Bool) (s : Finset E) (x : X) : Prop := ∃ e ∈ s, hit e x = true

noncomputable def errors (hit : E → X → Bool) (s t : Finset E) : Finset X := by
  classical
  exact Finset.univ.filter fun x => ¬ (accepts hit s x ↔ accepts hit t x)

theorem accepts_mono (hit : E → X → Bool) {s t : Finset E} (h : s ⊆ t) {x : X}
    (hx : accepts hit s x) : accepts hit t x := by
  obtain ⟨e,he,hh⟩ := hx
  exact ⟨e,h he,hh⟩

theorem added_errors (hit : E → X → Bool) {s t : Finset E} {e : E} (he : e ∈ t) :
    errors hit s (insert e s) ⊆ errors hit s t := by
  intro x hx
  simp [errors, accepts] at hx ⊢
  grind

theorem deleted_errors (hit : E → X → Bool) {s t : Finset E} {e : E}
    (h : t ⊆ s) (he : e ∉ t) : errors hit s (s.erase e) ⊆ errors hit s t := by
  have ht : t ⊆ s.erase e := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨fun eq => he (eq ▸ ha),h ha⟩
  intro x hx
  have a := accepts_mono hit (Finset.erase_subset e s) (x := x)
  have b := accepts_mono hit ht (x := x)
  simp only [errors, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  tauto

/-- A nearest distinct graph is a single edge edit. Each edge has an input
(private to that edge) setting exactly its two endpoints true. -/
theorem strict_if_further_edit (hit : E → X → Bool)
    (priv : E → X) (hp : ∀ a b, hit a (priv b) = decide (a = b))
    {s u t : Finset E} (sub : errors hit s u ⊆ errors hit s t)
    {b : E} (same : b ∈ u ↔ b ∈ s) (changed : ¬(b ∈ t ↔ b ∈ s)) :
    (errors hit s u).card < (errors hit s t).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩
  have spec (v : Finset E) : accepts hit v (priv b) ↔ b ∈ v := by simp [accepts,hp]
  have mem (v : Finset E) : priv b ∈ errors hit s v ↔ ¬ (b ∈ v ↔ b ∈ s) := by
    simp only [errors,Finset.mem_filter,Finset.mem_univ,true_and,spec]
    tauto
  intro eq
  have h1 := (mem t).mpr changed
  rw [← eq] at h1
  exact (mem u).mp h1 same
/-- For any distinct graph choose a single edit with no larger error set.
If the candidate also changes another edge, that inclusion is strict. -/
theorem single_edit_dominates (hit : E → X → Bool) (priv : E → X)
    (hp : ∀ a b, hit a (priv b) = decide (a = b))
    {s t : Finset E} (hne : t ≠ s) :
    ∃ u : Finset E,
      ((∃ e ∉ s, u = insert e s) ∨ (∃ e ∈ s, u = s.erase e)) ∧
      errors hit s u ⊆ errors hit s t ∧
      (u ≠ t → (errors hit s u).card < (errors hit s t).card) := by
  classical
  by_cases sub : t ⊆ s
  · have hn : ¬s ⊆ t := fun h => hne (Finset.Subset.antisymm sub h)
    obtain ⟨e,hs,ht⟩ := Finset.not_subset.mp hn
    have inc := deleted_errors hit sub ht
    refine ⟨s.erase e, Or.inr ⟨e,hs,rfl⟩, inc, ?_⟩
    intro ne
    have ts : t ⊆ s.erase e := fun b hb =>
      Finset.mem_erase.mpr ⟨fun h => ht (h ▸ hb),sub hb⟩
    obtain ⟨b,hu,hb⟩ := Finset.not_subset.mp (show ¬s.erase e ⊆ t from
      fun h => ne (Finset.Subset.antisymm h ts))
    have mem := Finset.mem_erase.mp hu
    exact strict_if_further_edit hit priv hp inc (b := b)
      ⟨fun _ => mem.2,fun _ => hu⟩ (fun eq => hb (eq.mpr mem.2))
  · obtain ⟨e,ht,hs⟩ := Finset.not_subset.mp sub
    have inc := added_errors hit (s := s) ht
    refine ⟨insert e s, Or.inl ⟨e,hs,rfl⟩, inc, ?_⟩
    intro ne
    obtain ⟨b,hb⟩ : ∃ b, ¬(b ∈ insert e s ↔ b ∈ t) := by
      by_contra! h
      exact ne (Finset.ext h)
    have be : b ≠ e := by rintro rfl; exact hb ⟨fun _ => ht, fun _ => Finset.mem_insert_self _ _⟩
    have eq : b ∈ insert e s ↔ b ∈ s := by simp [be]
    exact strict_if_further_edit hit priv hp inc eq (fun h => hb (eq.trans h.symm))

#print axioms single_edit_dominates
#print axioms accepts_mono
#print axioms added_errors
#print axioms deleted_errors
#print axioms strict_if_further_edit
end PEqualNP.Research.NearestGraph

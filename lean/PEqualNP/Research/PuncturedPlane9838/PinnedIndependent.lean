import Mathlib.Tactic
namespace PEqualNP.Research.PuncturedPlane9838
variable {V : Type*} [DecidableEq V]
/-- Edges can be listed in either orientation. -/
def independent (E : Finset (V × V)) (s : Finset V) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ s ∧ e.2 ∈ s)

omit [DecidableEq V] in
theorem independent_mono {E : Finset (V × V)} {s t : Finset V}
    (h : independent E t) (st : s ⊆ t) : independent E s :=
  fun e he ⟨a,b⟩ => h e he ⟨st a,st b⟩

def extensions (E : Finset (V × V)) (pins : Finset V) :=
  {s : Finset V // pins ⊆ s ∧ independent E s}

def residualSets (E : Finset (V × V)) (pins : Finset V) :=
  {r : Finset V // (∀ z ∈ r, z ∉ pins ∧ independent E (insert z pins)) ∧ independent E r}

/-- Fix the pins true, discard their neighbors, then choose any independent
set in the residual induced graph. This is a bijection, including empty pins. -/
def extensionEquiv (E : Finset (V × V)) (p : Finset V) (hp : independent E p) :
    extensions E p ≃ residualSets E p where
  toFun s := ⟨s.1 \ p, by
    constructor
    · intro z hz
      obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hz
      exact ⟨hn, independent_mono s.2.2 (Finset.insert_subset hs s.2.1)⟩
    · exact independent_mono s.2.2 Finset.sdiff_subset⟩
  invFun r := ⟨p ∪ r.1, by
    refine ⟨Finset.subset_union_left, ?_⟩
    intro e he hab
    obtain ⟨a,b⟩ := hab
    rcases Finset.mem_union.mp a with ap|ar <;> rcases Finset.mem_union.mp b with bp|br
    · exact hp e he ⟨ap,bp⟩
    · exact (r.2.1 _ br).2 e he ⟨Finset.mem_insert_of_mem ap, Finset.mem_insert_self ..⟩
    · exact (r.2.1 _ ar).2 e he ⟨Finset.mem_insert_self .., Finset.mem_insert_of_mem bp⟩
    · exact r.2.2 e he ⟨ar,br⟩⟩
  left_inv s := by
    apply Subtype.ext
    change p ∪ (s.1 \ p) = s.1
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have h := @s.2.1 z
    tauto
  right_inv r := by
    apply Subtype.ext
    change (p ∪ r.1) \ p = r.1
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h : z ∈ r.1 → z ∉ p := fun hz => (r.2.1 z hz).1
    tauto

theorem independent_insert_edge (E : Finset (V × V)) (u v : V) (s : Finset V) :
    independent (insert (u,v) E) s ↔ independent E s ∧ ¬(u ∈ s ∧ v ∈ s) := by
  simp [independent, and_comm]

theorem edge_error_iff (E : Finset (V × V)) (u v : V) (s : Finset V) :
    (independent E s ∧ ¬independent (insert (u,v) E) s) ↔
      ({u,v} : Finset V) ⊆ s ∧ independent E s := by
  rw [independent_insert_edge]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  tauto
end PEqualNP.Research.PuncturedPlane9838

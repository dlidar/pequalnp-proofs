import Mathlib

namespace PEqualNP.Research.NovelTrace

def bank {α} (S : Set (Set α)) (gs : List (Set α)) : Set (Set α) := S ∪ {v | v∈gs}
def derived {α} (B : Set (Set α)) (v : Set α) := ∃ a∈B, ∃ b∈B,v=a∪b ∨ v=a∩b
def legal {α} (S : Set (Set α)) (gs : List (Set α)) := ∀ j (hj:j<gs.length),
  gs[j] ∉ bank S (gs.take j) ∧ derived (bank S (gs.take j)) gs[j]

theorem snoc {α} {S : Set (Set α)} {gs : List (Set α)} {v : Set α}
    (h : legal S gs) (fresh : v ∉ bank S gs) (fromOld : derived (bank S gs) v) :
    legal S (gs++[v]) := by
  intro j hj
  by_cases was : j<gs.length
  · rw [List.getElem_append_left was,List.take_append_of_le_length (by omega)]
    exact h j was
  · have eq : j=gs.length := by simp at hj;omega
    subst j
    simpa using And.intro fresh fromOld

/-- Repeated wires can be dropped at each prefix, preserving every available set. -/
theorem normalize {α} (S : Set (Set α)) (gs : List (Set α))
    (h : ∀ j (hj:j<gs.length), gs[j] ∈ bank S (gs.take j) ∨ derived (bank S (gs.take j)) gs[j]) :
    ∃ ys : List (Set α), ys.length ≤ gs.length ∧ legal S ys ∧ bank S ys=bank S gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[],le_rfl,by simp [legal],rfl⟩
  | append_singleton gs v ih =>
    have prev : ∀ j (hj:j<gs.length), gs[j] ∈ bank S (gs.take j) ∨ derived (bank S (gs.take j)) gs[j] := by
      intro j hj
      have h2 := h j (by simp;omega)
      rwa [List.getElem_append_left hj,List.take_append_of_le_length (by omega)] at h2
    obtain ⟨ys,len,ok,same⟩ := ih prev
    have last : v ∈ bank S gs ∨ derived (bank S gs) v := by simpa using h gs.length (by simp)
    by_cases old : v ∈ bank S gs
    · refine ⟨ys,by simp;omega,ok,?_⟩
      rw [same]
      ext u; simp only [bank,Set.mem_union,Set.mem_setOf_eq,List.mem_append,List.mem_singleton]
      change v∈S ∨ v∈gs at old; aesop
    · refine ⟨ys++[v],by simp;omega,snoc ok (same ▸ old) (same ▸ last.resolve_left old),?_⟩
      ext u
      have point := Set.ext_iff.mp same u
      simp only [bank,Set.mem_union,Set.mem_setOf_eq,List.mem_append,List.mem_singleton] at *
      tauto

end PEqualNP.Research.NovelTrace

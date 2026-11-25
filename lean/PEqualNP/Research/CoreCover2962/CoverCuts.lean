import PEqualNP.Defs
import Mathlib.Tactic

/-! Exact accounting for the change of a bipartite minimum cover under edge deletion. -/
namespace PEqualNP.Research.CoreCoverCuts
open Finset PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ}
abbrev V (n : ℕ) := Fin n
def neighbors (G : SimpleGraph (V n)) [DecidableRel G.Adj] (A : Finset (V n)) :=
  univ.filter fun v => ∃ u ∈ A, G.Adj u v
def cut (G : SimpleGraph (V n)) [DecidableRel G.Adj] (L A : Finset (V n)) :=
  (L \ A) ∪ neighbors G A
def Parts (G : SimpleGraph (V n)) (L : Finset (V n)) : Prop :=
  ∀ u v, G.Adj u v → (u ∈ L ↔ v ∉ L)

theorem mem_neighbors {G : SimpleGraph (V n)} [DecidableRel G.Adj] {A : Finset (V n)} {v} :
    v ∈ neighbors G A ↔ ∃ u ∈ A, G.Adj u v := by simp [neighbors]

theorem cut_covers {G : SimpleGraph (V n)} [DecidableRel G.Adj] {L A : Finset (V n)}
    (parts : Parts G L) : G.IsVertexCover (cut G L A : Set (V n)) := by
  intro u v adj
  change u ∈ (L \ A) ∪ neighbors G A ∨ v ∈ (L \ A) ∪ neighbors G A
  simp only [Finset.mem_union, Finset.mem_sdiff, mem_neighbors]
  by_cases h : u ∈ L
  · by_cases p : u ∈ A
    · exact Or.inr (Or.inr ⟨u,p,adj⟩)
    · exact Or.inl (Or.inl ⟨h,p⟩)
  · have hv : v ∈ L := by by_contra q; exact h ((parts u v adj).mpr q)
    by_cases p : v ∈ A
    · exact Or.inl (Or.inr ⟨v,p,adj.symm⟩)
    · exact Or.inr (Or.inl ⟨hv,p⟩)

theorem residual_cut_subset {G : SimpleGraph (V n)} [DecidableRel G.Adj] {L T : Finset (V n)}
    (h : G.IsVertexCover (T : Set (V n))) : cut G L (L \ T) ⊆ T := by
  intro v hv
  rcases Finset.mem_union.mp hv with m | m
  · simp only [Finset.mem_sdiff] at m
    by_contra q; exact m.2 ⟨m.1,q⟩
  · obtain ⟨u,hu,adj⟩ := mem_neighbors.mp m
    exact (h adj).resolve_left (Finset.mem_sdiff.mp hu).2

theorem min_cover_cut {G : SimpleGraph (V n)} [DecidableRel G.Adj] {L T : Finset (V n)}
    (parts : Parts G L) (h : IsMinCover G T) : cut G L (L \ T) = T :=
  Finset.eq_of_subset_of_card_le (residual_cut_subset h.1) (h.2 _ (cut_covers parts))

theorem disjoint_neighbors {G : SimpleGraph (V n)} [DecidableRel G.Adj] {L A : Finset (V n)}
    (parts : Parts G L) (ha : A ⊆ L) : Disjoint L (neighbors G A) := by
  apply Finset.disjoint_left.mpr
  intro v hv m
  obtain ⟨u,hu,adj⟩ := mem_neighbors.mp m
  exact (parts u v adj).mp (ha hu) hv

theorem neighbors_mono_graph {G H : SimpleGraph (V n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : H ≤ G) (A : Finset (V n)) : neighbors H A ⊆ neighbors G A := by
  intro v hv
  obtain ⟨u,hu,adj⟩ := mem_neighbors.mp hv
  exact mem_neighbors.mpr ⟨u,hu,h adj⟩

theorem cut_change {G H : SimpleGraph (V n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {L A : Finset (V n)} (parts : Parts G L) (sub : H ≤ G) (ha : A ⊆ L) :
    (cut H L A).card + (neighbors G A \ neighbors H A).card = (cut G L A).card := by
  have pH : Parts H L := fun u v h => parts u v (sub h)
  have dG := (disjoint_neighbors parts ha).mono_left (Finset.sdiff_subset : L \ A ⊆ L)
  have dH := (disjoint_neighbors pH ha).mono_left (Finset.sdiff_subset : L \ A ⊆ L)
  simp only [cut, Finset.card_union_of_disjoint dG, Finset.card_union_of_disjoint dH,
    Finset.card_sdiff_of_subset (neighbors_mono_graph sub A)]
  have := Finset.card_le_card (neighbors_mono_graph sub A)
  omega

/-- All point subsets give valid tests. A minimum cover of H supplies one
subset attaining equality, even if its extension to G is far from minimum. -/
theorem budget_iff_all_cuts {G H : SimpleGraph (V n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {L T : Finset (V n)} (parts : Parts G L) (sub : H ≤ G) (ht : IsMinCover H T) (d b : ℕ) :
    d ≤ b + T.card ↔ ∀ A ⊆ L,
      d + (neighbors G A \ neighbors H A).card ≤ b + (cut G L A).card := by
  have ph : Parts H L := fun u v h => parts u v (sub h)
  constructor
  · intro good A ha
    have c := ht.2 (cut H L A) (cut_covers ph)
    have q := cut_change parts sub ha
    omega
  · intro all
    have q := all (L \ T) Finset.sdiff_subset
    have e := cut_change (A := L \ T) parts sub Finset.sdiff_subset
    rw [min_cover_cut ph ht] at e
    omega
end PEqualNP.Research.CoreCoverCuts

namespace PEqualNP.Research.CoreCoverCuts
open Finset PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitLowerBounds
variable {n : ℕ}

theorem parts_from_coloring {G : SimpleGraph (V n)} (s : V n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v) :
    Parts G (univ.filter fun u => s u = true) := by
  intro u v adj
  have h := bip u v adj
  simp only [mem_filter, mem_univ, true_and]
  cases hu : s u <;> cases hv : s v <;> simp_all

/-- Replaces the change of optimum by lost neighbors minus the excess cost of
the original cut, with no subtraction or sign convention required. -/
theorem cover_budget_iff {G H : SimpleGraph (V n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {L T T' : Finset (V n)} (p : Parts G L) (sub : H ≤ G) (t : IsMinCover G T)
    (t' : IsMinCover H T') (e b : ℕ) :
    e + T.card ≤ b + T'.card ↔ ∀ A ⊆ L, e + (neighbors G A \ neighbors H A).card ≤
      b + ((cut G L A).card - T.card) := by
  rw [budget_iff_all_cuts p sub t' (e + T.card) b]
  constructor <;> intro h A ha <;> have q := h A ha <;>
    have w := t.2 (cut G L A) (cut_covers p) <;> omega

theorem core_budget_iff (G : SimpleGraph (V n)) [DecidableRel G.Adj] (C : Circuit)
    (s : V n → Bool) (bip : ∀ u v, G.Adj u v → s u ≠ s v) (T T' : Finset (V n)) :
    let M := PEqualNP.Core.maximalCores G C
    let D := M.biUnion (PEqualNP.TopForm.gammaE G C)
    let U := M.biUnion (PEqualNP.Core.coneSet n C)
    let H := G.deleteEdges (D : Set (Sym2 (V n)))
    let L := univ.filter fun u => s u = true
    IsMinCover G T → IsMinCover H T' →
      (D.card + T.card ≤ U.card + M.card + T'.card ↔
        ∀ A ⊆ L, D.card + (neighbors G A \ neighbors H A).card ≤
          U.card + M.card + ((cut G L A).card - T.card)) := by
  dsimp only
  intro t t'
  exact cover_budget_iff (parts_from_coloring s bip) (G.deleteEdges_le _) t t' _ _

end PEqualNP.Research.CoreCoverCuts

namespace PEqualNP.Research.CoreCoverCuts
open Finset PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ}

def closure (H : SimpleGraph (V n)) [DecidableRel H.Adj] (L A : Finset (V n)) :=
  L.filter fun u => neighbors H {u} ⊆ neighbors H A

theorem subset_closure {H : SimpleGraph (V n)} [DecidableRel H.Adj] {L A : Finset (V n)}
    (a : A ⊆ L) : A ⊆ closure H L A := by
  intro u hu
  apply mem_filter.mpr
  refine ⟨a hu, fun v hv => ?_⟩
  obtain ⟨w,hw,adj⟩ := mem_neighbors.mp hv
  exact mem_neighbors.mpr ⟨u,hu,Finset.mem_singleton.mp hw ▸ adj⟩

theorem closure_neighbors {H : SimpleGraph (V n)} [DecidableRel H.Adj] {L A : Finset (V n)}
    (a : A ⊆ L) : neighbors H (closure H L A) = neighbors H A := by
  ext v
  constructor <;> intro hv
  · obtain ⟨u,hu,adj⟩ := mem_neighbors.mp hv
    exact (mem_filter.mp hu).2 (mem_neighbors.mpr ⟨u,mem_singleton_self u,adj⟩)
  · obtain ⟨u,hu,adj⟩ := mem_neighbors.mp hv
    exact mem_neighbors.mpr ⟨u,subset_closure a hu,adj⟩

theorem closure_idem {H : SimpleGraph (V n)} [DecidableRel H.Adj] {L A : Finset (V n)}
    (a : A ⊆ L) : closure H L (closure H L A) = closure H L A := by
  unfold closure at *
  rw [show neighbors H (L.filter fun u => neighbors H {u} ⊆ neighbors H A) = neighbors H A from
    closure_neighbors a]

theorem residual_closed {H : SimpleGraph (V n)} [DecidableRel H.Adj] {L T : Finset (V n)}
    (p : Parts H L) (h : IsMinCover H T) : closure H L (L \ T) = L \ T := by
  let A := L \ T
  have ha : A ⊆ L := sdiff_subset
  have inc := subset_closure (H := H) ha
  have sub : cut H L (closure H L A) ⊆ cut H L A := by
    unfold cut
    rw [closure_neighbors ha]
    exact Finset.union_subset_union (Finset.sdiff_subset_sdiff (by rfl) inc) (by rfl)
  have orig : cut H L A = T := min_cover_cut p h
  have equal : cut H L (closure H L A) = cut H L A := by
    apply eq_of_subset_of_card_le sub
    rw [orig]
    exact h.2 _ (cut_covers p)
  apply Subset.antisymm _ inc
  intro u hu
  have hl : u ∈ L := (mem_filter.mp hu).1
  by_contra notA
  have hc : u ∈ cut H L A := mem_union_left _ (mem_sdiff.mpr ⟨hl,notA⟩)
  rw [← equal] at hc
  rcases mem_union.mp hc with q | q
  · exact (mem_sdiff.mp q).2 hu
  · rw [closure_neighbors ha] at q
    exact disjoint_left.mp (disjoint_neighbors p ha) hl q

theorem budget_iff_closed_cuts {G H : SimpleGraph (V n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {L T T' : Finset (V n)} (p : Parts G L) (sub : H ≤ G) (t : IsMinCover G T)
    (t' : IsMinCover H T') (e b : ℕ) :
    e + T.card ≤ b + T'.card ↔ ∀ A ⊆ L, closure H L A = A →
      e + (neighbors G A \ neighbors H A).card ≤ b + ((cut G L A).card - T.card) := by
  have ph : Parts H L := fun u v h => p u v (sub h)
  constructor
  · exact fun h A ha _ => (cover_budget_iff p sub t t' e b).mp h A ha
  · intro tests
    have q := tests (L \ T') sdiff_subset (residual_closed ph t')
    have c := cut_change (A := L \ T') p sub sdiff_subset
    rw [min_cover_cut ph t'] at c
    have := t.2 (cut G L (L \ T')) (cut_covers p)
    omega

end PEqualNP.Research.CoreCoverCuts

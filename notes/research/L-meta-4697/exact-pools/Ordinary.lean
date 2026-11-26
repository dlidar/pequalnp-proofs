import Girth
import PEqualNP.MetaComplexity.Helpers.EdgeUpper
namespace PEqualNP.Research.Pool4697
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem ordinary_upper {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n)) (cov : G.IsVertexCover ↑K) (edge : ∃ a b,G.Adj a b) :
    HasCircuitSize n (graphFun G ∅) (G.edgeSet.ncard+K.card-1) := by
  have h := Helpers.EdgeUpper.edge_upper n G K edge (fun a b e => cov e)
  have same : G.edgeSet.ncard = G.edgeFinset.card := by rw [Set.ncard_eq_toFinset_card'];rfl
  rw [same]
  have hf : graphFun G ∅ = (fun x => decide (∃ i j,G.Adj i j ∧ x i=true ∧ x j=true)) := by
    funext x
    simp [graphFun]
  rwa [hf]

theorem ordinary_exact_of_posted (posted : Posted)
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A K : Finset (Fin n))
    (cubic : ∀ v ∉ A,(G.neighborSet v).ncard=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length)
    (iso : ∀ a b,G.Adj a b → a∉A) (edge : ∃ a b,G.Adj a b) (minK : IsMinCover G K) (s : Nat) :
    HasCircuitSize n (graphFun G ∅) s ↔ G.edgeSet.ncard+K.card-1 ≤ s := by
  constructor
  · intro size
    obtain ⟨T,c,h⟩ := posted_iff.mp posted n G A cubic girth iso edge s size
    have small := minK.2 T c
    omega
  · intro le
    obtain ⟨C,f,sz,ok⟩ := ordinary_upper G K minK.1 edge
    exact ⟨C,f,sz.trans le,ok⟩
end PEqualNP.Research.Pool4697

namespace PEqualNP.Research.Example4697
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Research.Pool4697
theorem ordinary_49 : HasCircuitSize 24 (graphFun G ∅) 49 := by
  have h := ordinary_upper G witness cover_witness ⟨0,1,by decide +kernel⟩
  simpa [edge_count,witness_size] using h
theorem saving_refutes_assignment (h : HasCircuitSize 24 (graphFun G ∅) 48) : ¬ Posted := by
  intro posted
  have bad := required_49 posted 48 h
  omega
end PEqualNP.Research.Example4697

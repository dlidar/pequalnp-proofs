import PEqualNP.Research.CleanStars3321
import PEqualNP.Research.ForestCase6390

namespace PEqualNP.Research.ForestNormal3321
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17442 PEqualNP.Research.CleanStars3321
open PEqualNP.Research.ForestCase6390

def Target {p l : ℕ} (E : Finset (Fin p × Fin l)) (z : Fin (p+l) → Bool) : Prop :=
  ∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd l i) = true ∧ z (Fin.natAdd p j) = true

def Below {p l : ℕ} (E : Finset (Fin p × Fin l)) (D : Circuit) : Prop :=
  ∀ j < D.gates.length, (NestedCover.gateAt D j).op = .and →
    ∀ z : Fin (p+l) → Bool, (D.wires (List.ofFn z)).getD (p+l+j) false = true → Target E z

theorem compile_cover {p l : ℕ} (E : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l))
    (cover : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧
      D.size ≤ E.card + P.card + L.card - 1 ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ Below E D := by
  classical
  let A := E.filter fun e => e.1 ∈ P
  let B := E \ A
  have sub : A ⊆ E := filter_subset _ _
  have union : A ∪ B = E := by simp [B,sub,Finset.union_sdiff_of_subset]
  have nE : A.card + B.card = E.card := by dsimp [B];rw [card_sdiff_of_subset sub];have := card_le_card sub;omega
  have left : A.image Prod.fst ⊆ P := by
    rintro i hi;obtain ⟨e,he,rfl⟩ := mem_image.mp hi;exact (mem_filter.mp he).2
  have right : B.image Prod.snd ⊆ L := by
    rintro j hj;obtain ⟨e,he,rfl⟩ := mem_image.mp hj
    obtain ⟨h,na⟩ := mem_sdiff.mp he
    exact (cover e h).resolve_left (fun hp => na (mem_filter.mpr ⟨h,hp⟩))
  obtain ⟨own,tag,edges,sum,len⟩ := Construction.makeOwners p l A B
  let D := coverCircuitB (p+l) own
  obtain ⟨sz,ev⟩ := Evaluation p l (fun i j => (i,j) ∈ A ∪ B) own tag edges
  obtain ⟨_,_,ao,_⟩ := Topology p l own tag
  have size : D.size ≤ E.card+P.card+L.card-1 := by
    rw [sz,sum,len];have := card_le_card left;have := card_le_card right;omega
  have computes : ∀ z, circuitFun (p+l) D z = true ↔ Target E z := by
    intro z;rw [ev,union,decide_eq_true_eq];rfl
  have valid : ∀ o ∈ own, o.1 < p+l ∧ ∀ r ∈ o.2, r < p+l := by
    intro o ho
    rcases (tag o ho).2 with ⟨h,hs⟩|⟨_,h,hs⟩
    · exact ⟨by omega,fun r hr => (hs r hr).2⟩
    · exact ⟨h,fun r hr => by have := hs r hr;omega⟩
  refine ⟨D,ao,size,computes,?_⟩
  intro j hj op z val
  by_contra hn
  have no : circuitFun (p+l) D z = false := Bool.eq_false_iff.mpr (fun on => hn ((computes z).mp on))
  have bad := no_and_on_reject (p+l) own valid (fun o ho => (tag o ho).1) z no j hj op
  rw [bad] at val
  cases val

theorem forest_normal {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (forest : ∀ v (c : (graph E).Walk v v), ¬ c.IsCycle) (fan : FanInTwo C)
    (computes : ∀ z, circuitFun (p+l) C z = true ↔ Target E z) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ Below E D := by
  classical
  have exactC : ∀ z, circuitFun (p+l) C z =
      decide (∃ e ∈ E, z (Fin.castAdd l e.1) = true ∧ z (Fin.natAdd p e.2) = true) := by
    intro z
    apply Bool.eq_iff_iff.mpr
    rw [computes,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,h,a,b⟩;exact ⟨(i,j),h,a,b⟩
    · rintro ⟨⟨i,j⟩,h,a,b⟩;exact ⟨i,j,h,a,b⟩
  obtain ⟨P,L,cov,bt⟩ := forest_case E C forest fan exactC
  obtain ⟨D,model,bound,ev,ok⟩ := compile_cover E P L cov
  exact ⟨D,model,by omega,ev,ok⟩

end PEqualNP.Research.ForestNormal3321

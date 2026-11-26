import PEqualNP.Research.PureReadTwo
import PEqualNP.Research.ForestCase6390

namespace PEqualNP.Research.ForestReadTwo
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17442 PEqualNP.Research.PureReadTwo PEqualNP.Research.ReadTwoIncidence
open PEqualNP.Research.ForestCase6390

def Target {p l : ℕ} (E : Finset (Fin p × Fin l)) (z : Fin (p+l) → Bool) : Prop :=
  ∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd l i) = true ∧ z (Fin.natAdd p j) = true

theorem compile_cover {p l : ℕ} (E : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l))
    (cover : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧
      D.size ≤ E.card + P.card + L.card - 1 ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ PEqualNP.ReadK.IsReadK (p+l) D 2 := by
  classical
  let A := E.filter fun e => e.1 ∈ P
  let B := E \ A
  have sub : A ⊆ E := filter_subset _ _
  have union : A ∪ B = E := by simp [B,sub]
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
  obtain ⟨X,Y,ao,hX,hY,hAnd⟩ := Topology p l own tag
  have size : D.size ≤ E.card+P.card+L.card-1 := by
    rw [sz,sum,len];have := card_le_card left;have := card_le_card right;omega
  have computes : ∀ z, circuitFun (p+l) D z = true ↔ Target E z := by
    intro z;rw [ev,union,decide_eq_true_eq];rfl
  refine ⟨D,ao,size,computes,?_⟩
  apply by_topology (fun i j => (i,j) ∈ E) D ao
    (fun z => Bool.eq_iff_iff.mpr (by rw [computes]; simp [incidence,Target])) (X ∪ Y)
  intro j hj
  let g := NestedCover.gateAt D j
  have eq : D.gates[j] = g := by
    have h := Topology.Helpers.gateAt_get D j hj
    rw [List.getElem?_eq_getElem hj] at h
    exact Option.some.inj h
  rw [eq]
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hx|hy
    · rcases hX _ hx with lo | ⟨k,_,idx,op,src⟩
      · omega
      · have e : j=k := by omega
        subst k
        exact ⟨op,fun t ht => Finset.mem_union_left Y (src t ht)⟩
    · rcases hY _ hy with ⟨_,lo⟩ | ⟨k,_,idx,op,src⟩
      · omega
      · have e : j=k := by omega
        subst k
        exact ⟨op,fun t ht => Finset.mem_union_right X (src t ht)⟩
  · intro op t ht
    obtain ⟨a,b,ab,orient⟩ := hAnd j hj op
    change t ∈ (NestedCover.gateAt D j).inputs at ht
    rw [ab] at ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases orient with ⟨ha,hb⟩|⟨ha,hb⟩ <;> rcases ht with rfl|rfl <;>
      first | exact Finset.mem_union_left _ ha | exact Finset.mem_union_right _ hb |
        exact Finset.mem_union_right _ ha | exact Finset.mem_union_left _ hb

theorem forest_normal {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (forest : ∀ v (c : (graph E).Walk v v), ¬ c.IsCycle) (fan : FanInTwo C)
    (computes : ∀ z, circuitFun (p+l) C z = true ↔ Target E z) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ PEqualNP.ReadK.IsReadK (p+l) D 2 := by
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

end PEqualNP.Research.ForestReadTwo

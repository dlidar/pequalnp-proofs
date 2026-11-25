import PEqualNP.MetaComplexity.Helpers.LiveSize
import PEqualNP.Research.CoreCover2962.CoverCuts
import Mathlib.Tactic

/-! Count every operand position in a union of overlapping cones, including
repeated operands of one gate. Distinct gate wires are exactly the non-roots. -/
namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LiveSize PEqualNP.Core PEqualNP.EdgeOwnership PEqualNP.TopForm

def conesOf (n : Nat) (C : Circuit) (M : Finset Nat) := M.biUnion (coneSet n C)
def operands (C : Circuit) (U : Finset Nat) := U.biUnion fun j => (gateAt C j).inputs.toFinset
def raw (n : Nat) (C : Circuit) (U : Finset Nat) := (operands C U).filter (· < n)
def repeated (C : Circuit) (U : Finset Nat) :=
  (∑ j ∈ U, (gateAt C j).inputs.length) - (operands C U).card

theorem mem_operands {C U w} : w ∈ operands C U ↔ ∃ j ∈ U, w ∈ (gateAt C j).inputs := by
  simp [operands]
theorem mem_conesOf {n C M i} : i ∈ conesOf n C M ↔
    ∃ j ∈ M, i = j ∨ (i < C.gates.length ∧ InCone n C i j) := by
  simp [conesOf,coneSet]
theorem roots_subset (n C M) : M ⊆ conesOf n C M :=
  fun j h => mem_conesOf.mpr ⟨j,h,Or.inl rfl⟩

theorem internally_read {n C M} (back : ReadsBack n C)
    (valid : ∀ j ∈ M, j < C.gates.length)
    (anti : ∀ i ∈ M, ∀ j ∈ M, ¬ InCone n C i j) (i : Nat) :
    n+i ∈ operands C (conesOf n C M) ↔ i ∈ conesOf n C M \ M := by
  constructor
  · intro h
    obtain ⟨g,hg,read⟩ := mem_operands.mp h
    obtain ⟨j,hj,rg⟩ := mem_conesOf.mp hg
    have gl : g < C.gates.length := rg.elim (fun e => e ▸ valid j hj) And.left
    have less := back g gl _ read
    have step : RR n C i g := ⟨gl,by omega,read⟩
    have reach : Relation.TransGen (RR n C) i j := by
      rcases rg with rfl | ⟨_,path⟩
      · exact .single step
      · exact .head step ((cone_iff ..).mp path)
    have cone := (cone_iff ..).mpr reach
    exact mem_sdiff.mpr ⟨mem_conesOf.mpr ⟨j,hj,Or.inr ⟨by omega,cone⟩⟩,fun m => anti i m j hj cone⟩
  · intro h
    obtain ⟨hi,nm⟩ := mem_sdiff.mp h
    obtain ⟨j,hj,e | ⟨_,cone⟩⟩ := mem_conesOf.mp hi
    · exact False.elim (nm (e ▸ hj))
    obtain ⟨g,rr,path⟩ := Relation.TransGen.head'_iff.mp ((cone_iff ..).mp cone)
    apply mem_operands.mpr
    refine ⟨g,mem_conesOf.mpr ⟨j,hj,?_⟩,rr.2.2⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with e | q
    · exact Or.inl e.symm
    · exact Or.inr ⟨rr.1,(cone_iff ..).mpr q⟩

theorem count_wires {n C M} (ao : IsAO2 n C)
    (valid : ∀ j ∈ M, j < C.gates.length)
    (anti : ∀ i ∈ M, ∀ j ∈ M, ¬ InCone n C i j) :
    let U := conesOf n C M
    U.card + M.card = (raw n C U).card + repeated C U := by
  let U := conesOf n C M
  let W := operands C U
  change U.card + M.card = (raw n C U).card + repeated C U
  have eq : W.filter (fun w => ¬ w < n) = (U \ M).image (fun i => n+i) := by
    ext w
    constructor
    · intro h
      obtain ⟨hw,hn⟩ := mem_filter.mp h
      have ew : n + (w-n) = w := by omega
      exact mem_image.mpr ⟨w-n,(internally_read ao.2.1 valid anti _).mp (by rw [ew]; exact hw),ew⟩
    · intro h
      obtain ⟨i,m,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(internally_read ao.2.1 valid anti _).mpr m,by omega⟩
  have split := card_filter_add_card_filter_not (s := W) (fun w => w < n)
  rw [eq,card_image_of_injective _ (by intro a b h; dsimp at h; omega),
    card_sdiff_of_subset (roots_subset n C M)] at split
  have len (j) (m : j ∈ U) : (gateAt C j).inputs.length = 2 := by
    obtain ⟨i,hm,e⟩ := mem_conesOf.mp m
    have hj : j < C.gates.length := e.elim (fun e => e ▸ valid i hm) And.left
    apply ao.2.2
    simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  have tot : (∑ j ∈ U, (gateAt C j).inputs.length) = U.card * 2 := by
    calc _ = ∑ _j ∈ U, 2 := sum_congr rfl len
         _ = _ := by simp
  have le : W.card ≤ ∑ j ∈ U, (gateAt C j).inputs.length := by
    exact (Finset.card_biUnion_le).trans (sum_le_sum (fun j _ => List.toFinset_card_le _))
  have mU : M.card ≤ U.card := card_le_card (roots_subset n C M)
  change U.card + M.card = (W.filter (· < n)).card + ((∑ j ∈ U, (gateAt C j).inputs.length) - W.card)
  change (W.filter (· < n)).card + (U.card - M.card) = W.card at split
  omega

theorem maximal_core_wires (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) :
    let M := maximalCores G C
    let U := conesOf n C M
    U.card + M.card = (raw n C U).card + repeated C U := by
  apply count_wires ao
  · intro j hj
    exact mem_range.mp (mem_filter.mp hj).1
  · intro i hi j hj
    exact (mem_filter.mp hi).2.2 j (mem_range.mp (mem_filter.mp hj).1) (mem_filter.mp hj).2.1

end PEqualNP.Research.ConeWires

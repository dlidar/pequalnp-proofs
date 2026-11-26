import PEqualNP.Research.Residual6752
import PEqualNP.Research.ResidualConnection6752

namespace PEqualNP.Research.Overlap6752

open PEqualNP.Research.Residual6752 PEqualNP.Research.ResidualConnection6752
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

def asBlock (v : Fin 11) : Fin 14 := v.castLE (by decide)

theorem asBlock_injective : Function.Injective asBlock :=
  fun _ _ e => Fin.ext (congrArg (fun i : Fin 14 => i.val) e)

theorem touches (S : Finset (Fin 11)) (e : Edge) : e ∈ touched S ↔ ∃ v ∈ S, v ∈ e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [touched_iff]
    constructor
    · rintro (ha | hb)
      · exact ⟨a,ha,Sym2.mem_mk_left _ _⟩
      · exact ⟨b,hb,Sym2.mem_mk_right _ _⟩
    · rintro ⟨v,hv,hit⟩
      rcases Sym2.mem_iff.mp hit with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv

theorem incident_edges (S : Finset (Fin 11)) :
    touched S ∩ graph.edgeFinset = ((S.image asBlock).biUnion block).image edge := by
  ext e
  constructor
  · intro he
    obtain ⟨hit, ge⟩ := Finset.mem_inter.mp he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (edge_list.symm ▸ ge)
    obtain ⟨v,hv,hi⟩ := (touches S _).mp hit
    exact Finset.mem_image.mpr ⟨i,Finset.mem_biUnion.mpr
      ⟨asBlock v, Finset.mem_image_of_mem asBlock hv,(star_incidence v i).2 hi⟩,rfl⟩
  · intro he
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a,ha,hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_inter.mpr ⟨(touches S _).mpr ⟨v,hv,(star_incidence v i).1 hi⟩,
      edge_list ▸ Finset.mem_image_of_mem edge (Finset.mem_univ i)⟩

def minimum (t : Nat) : Nat := 66 - (11-t+1).choose 2 - starCapacity t

theorem overlap_lower (S : Finset (Fin 11)) : minimum S.card ≤ (forced graph S).card := by
  have h := (capacities (S.image asBlock)).2.1 (by
    intro a ha
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ha
    exact v.isLt)
  rw [Finset.card_image_of_injective _ asBlock_injective] at h
  rw [forced_card,incident_edges,Finset.card_image_of_injective _ edge_injective]
  exact Nat.sub_le_sub_left h _

def witness : Fin 12 → Finset (Fin 11)
  | 0 => ∅
  | 1 => {8}
  | 2 => {8,10}
  | 3 => {7,8,10}
  | 4 => {3,8,9,10}
  | 5 => {0,5,7,8,10}
  | 6 => {0,1,5,7,8,10}
  | 7 => {0,1,3,5,7,8,10}
  | 8 => {0,1,2,3,5,7,8,10}
  | 9 => {0,1,2,3,4,5,7,8,10}
  | 10 => {0,1,2,3,4,5,6,7,8,10}
  | _ => Finset.univ

theorem exact_examples : ∀ t : Fin 12,
    (witness t).card = t.val ∧ (forced graph (witness t)).card = minimum t := by decide +kernel

theorem table : ∀ t : Fin 12, minimum t =
    [0,7,13,19,25,31,36,40,44,47,49,50][t.val]! := by decide +kernel

-- The counted objects are distinct unordered false inputs accepted at this junk gate.
theorem junk_errors (C : Circuit) (ao : IsAO2 11 C) {g : Nat} (hg : g ∈ junk graph C)
    (S : Finset (Fin 11)) (shared : ∀ b : Fin 2, S ⊆ side C g b) :
    ∃ errors : Finset Edge, minimum S.card ≤ errors.card ∧
      ∀ u v : Fin 11, s(u,v) ∈ errors →
        PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ (pairInput u v) = false ∧
        gateVal 11 C g (pairInput u v) = true :=
  ⟨forced graph S, overlap_lower S, fun _ _ h => ⟨forced_negative graph S h, forced_gate graph ao hg S shared h⟩⟩

end PEqualNP.Research.Overlap6752

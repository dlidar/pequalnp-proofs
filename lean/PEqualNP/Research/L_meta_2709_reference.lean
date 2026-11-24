import PEqualNP.Defs

namespace PEqualNP.Research.HeawoodFactors
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]

def reference : Circuit :=
  ⟨[⟨.or,[7,8]⟩,
    ⟨.or,[14,10]⟩,
    ⟨.and,[0,15]⟩,
    ⟨.or,[7,9]⟩,
    ⟨.or,[17,13]⟩,
    ⟨.and,[1,18]⟩,
    ⟨.or,[8,12]⟩,
    ⟨.or,[20,13]⟩,
    ⟨.and,[2,21]⟩,
    ⟨.or,[7,11]⟩,
    ⟨.or,[23,12]⟩,
    ⟨.and,[3,24]⟩,
    ⟨.or,[10,11]⟩,
    ⟨.or,[26,13]⟩,
    ⟨.and,[4,27]⟩,
    ⟨.or,[9,10]⟩,
    ⟨.or,[29,12]⟩,
    ⟨.and,[5,30]⟩,
    ⟨.or,[8,9]⟩,
    ⟨.or,[32,11]⟩,
    ⟨.or,[16,19]⟩,
    ⟨.or,[34,22]⟩,
    ⟨.or,[35,25]⟩,
    ⟨.or,[36,28]⟩,
    ⟨.or,[37,31]⟩,
    ⟨.or,[38,6]⟩,
    ⟨.or,[38,33]⟩],40⟩

def edge (x : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 14, (p.val,l.val) ∈ edges ∧ x p = true ∧ x l = true
def wire (C : Circuit) (w : ℕ) (x : Fin 14 → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem edge_list (x : Fin 14 → Bool) :
    edge x ↔ (edges.any fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p,l,mem,ha,hb⟩
    refine ⟨(p.val,l.val),mem,?_⟩
    rw [Bool.and_eq_true]
    constructor
    · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact p.isLt),List.getElem_ofFn]
      exact ha
    · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact l.isLt),List.getElem_ofFn]
      exact hb
  · rintro ⟨⟨p,l⟩,mem,h⟩
    have bounded : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by decide
    obtain ⟨hp,hl⟩ := bounded _ mem
    refine ⟨⟨p,hp⟩,⟨l,hl⟩,mem,?_⟩
    simpa only [List.getD_eq_getElem _ _ (show p < (List.ofFn x).length by simpa using hp),
      List.getD_eq_getElem _ _ (show l < (List.ofFn x).length by simpa using hl),
      List.getElem_ofFn,Bool.and_eq_true] using h

-- A seven-star cover, with the last star distributed over the preceding six.
-- The prefix has 27 gates. Both factors are essential on negative inputs.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem reference_spec :
    Monotone2 reference ∧ reference.size = 27 ∧
    (∀ x : Fin 14 → Bool, edge x ↔ (wire reference 39 x && wire reference 40 x) = true) ∧
    (∃ x, ¬edge x ∧ wire reference 39 x = false ∧ wire reference 40 x = true) ∧
    (∃ x, ¬edge x ∧ wire reference 40 x = false ∧ wire reference 39 x = true) := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · simp [Monotone2,reference]
  · intro x
    rw [edge_list]
    simp [wire,reference,edges,Circuit.wires,GateOp.eval,List.ofFn_succ,List.getD]
    rw [← or_and_left]
    simp only [and_or_left, or_assoc]
  · refine ⟨fun i => (16256 : ℕ).testBit i.val,?_,?_,?_⟩ <;> first | (unfold edge; decide) | decide
  · refine ⟨fun i => (13504 : ℕ).testBit i.val,?_,?_,?_⟩ <;> first | (unfold edge; decide) | decide

end PEqualNP.Research.HeawoodFactors

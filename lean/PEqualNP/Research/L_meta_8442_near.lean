import Mathlib
import PEqualNP.Defs.MetaComplexity

namespace PEqualNP.Research.BridgeNeighbor

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem thirteen : PEqualNP.MetaComplexity.HasCircuitSize 8 target 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or,[1,2]⟩,⟨.or,[3,8]⟩,⟨.and,[0,9]⟩,⟨.and,[1,2]⟩,⟨.or,[10,11]⟩,
    ⟨.or,[6,7]⟩,⟨.or,[4,13]⟩,⟨.and,[5,14]⟩,⟨.and,[6,7]⟩,⟨.or,[15,16]⟩,
    ⟨.and,[3,4]⟩,⟨.or,[12,17]⟩,⟨.or,[18,19]⟩],20⟩
  refine ⟨C,?_,by decide +kernel,?_⟩
  · intro gate hg
    change gate ∈ C.gates at hg
    simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

def nearby : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or,[7,5]⟩,⟨.or,[2,3]⟩,⟨.and,[0,9]⟩,⟨.or,[3,5]⟩,⟨.or,[7,4]⟩,
  ⟨.or,[2,0]⟩,⟨.and,[1,13]⟩,⟨.and,[6,8]⟩,⟨.or,[14,15]⟩,⟨.and,[11,12]⟩,
  ⟨.or,[10,16]⟩,⟨.or,[17,18]⟩],19⟩

theorem nearby_size : nearby.size = 12 := rfl

theorem nearby_fanin : PEqualNP.MetaComplexity.FanInTwo nearby := by
  intro gate hg
  simp only [nearby,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by simp,by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nearby_adds_one_edge : ∀ x : Fin 8 → Bool, nearby.eval (List.ofFn x) =
    (target x || (x 3 && x 7)) := by
  decide +kernel

theorem nearby_exceptions : ∀ r : Fin 256,
    let x : Fin 8 → Bool := fun i => r.val.testBit i.val
    nearby.eval (List.ofFn x) ≠ target x ↔
    r.val ∈ ([136,138,140] : List Nat) := by
  intro r
  dsimp only
  rw [nearby_adds_one_edge]
  revert r
  decide +kernel

theorem repaired_graph : PEqualNP.MetaComplexity.HasCircuitSize 8
    (fun x => target x || (x 3 && x 7)) 12 :=
  ⟨nearby, nearby_fanin, le_of_eq nearby_size, nearby_adds_one_edge⟩

end PEqualNP.Research.BridgeNeighbor

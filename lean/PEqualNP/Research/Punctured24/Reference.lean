import Std.Tactic.BVDecide
import PEqualNP.Defs.MetaComplexity
import Mathlib.Tactic
namespace PEqualNP.Research.Punctured24
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def exactCircuit : Circuit := ⟨[⟨.or, [12,16]⟩, ⟨.or, [24,22]⟩, ⟨.and, [0,25]⟩, ⟨.or, [13,17]⟩, ⟨.or, [27,23]⟩, ⟨.and, [1,28]⟩, ⟨.or, [12,13]⟩, ⟨.or, [30,14]⟩, ⟨.or, [31,18]⟩, ⟨.and, [2,32]⟩, ⟨.or, [14,15]⟩, ⟨.or, [34,19]⟩, ⟨.and, [3,35]⟩, ⟨.or, [13,15]⟩, ⟨.or, [37,16]⟩, ⟨.or, [38,20]⟩, ⟨.and, [4,39]⟩, ⟨.or, [14,16]⟩, ⟨.or, [41,17]⟩, ⟨.or, [42,21]⟩, ⟨.and, [5,43]⟩, ⟨.or, [15,17]⟩, ⟨.or, [45,18]⟩, ⟨.or, [46,22]⟩, ⟨.and, [6,47]⟩, ⟨.or, [16,18]⟩, ⟨.or, [49,19]⟩, ⟨.or, [50,23]⟩, ⟨.and, [7,51]⟩, ⟨.or, [12,17]⟩, ⟨.or, [53,19]⟩, ⟨.or, [54,20]⟩, ⟨.and, [8,55]⟩, ⟨.or, [18,20]⟩, ⟨.or, [57,21]⟩, ⟨.and, [9,58]⟩, ⟨.or, [13,19]⟩, ⟨.or, [60,21]⟩, ⟨.or, [61,22]⟩, ⟨.and, [10,62]⟩, ⟨.or, [14,20]⟩, ⟨.or, [64,22]⟩, ⟨.or, [65,23]⟩, ⟨.and, [11,66]⟩, ⟨.or, [26,29]⟩, ⟨.or, [68,33]⟩, ⟨.or, [69,36]⟩, ⟨.or, [70,40]⟩, ⟨.or, [71,44]⟩, ⟨.or, [72,48]⟩, ⟨.or, [73,52]⟩, ⟨.or, [74,56]⟩, ⟨.or, [75,59]⟩, ⟨.or, [76,63]⟩, ⟨.or, [77,67]⟩],78⟩
def exactCircuitFn (x : Fin 24 → Bool) : Bool := (x 0 && x 12) || (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 12) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 12) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23)
theorem exactCircuit_size : exactCircuit.size = 55 := rfl
theorem exactCircuit_fan : FanInTwo exactCircuit := by simp [exactCircuit, FanInTwo]
theorem exactCircuit_eval (x : Fin 24 → Bool) : exactCircuit.eval (List.ofFn x) = exactCircuitFn x := by
  simp [exactCircuit, exactCircuitFn, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD, Bool.and_or_distrib_left, Bool.or_assoc]
theorem exactCircuit_bound : HasCircuitSize 24 exactCircuitFn 55 :=
  ⟨exactCircuit,exactCircuit_fan, Nat.le_of_eq exactCircuit_size,exactCircuit_eval⟩

def nearCircuit : Circuit := ⟨[⟨.or, [12,16]⟩, ⟨.or, [24,22]⟩, ⟨.and, [0,25]⟩, ⟨.or, [13,17]⟩, ⟨.or, [27,23]⟩, ⟨.and, [1,28]⟩, ⟨.or, [12,14]⟩, ⟨.or, [30,18]⟩, ⟨.and, [2,31]⟩, ⟨.or, [14,15]⟩, ⟨.or, [33,19]⟩, ⟨.and, [3,34]⟩, ⟨.or, [13,15]⟩, ⟨.or, [36,16]⟩, ⟨.or, [37,20]⟩, ⟨.and, [4,38]⟩, ⟨.or, [14,16]⟩, ⟨.or, [40,17]⟩, ⟨.or, [41,21]⟩, ⟨.and, [5,42]⟩, ⟨.or, [15,17]⟩, ⟨.or, [44,18]⟩, ⟨.or, [45,22]⟩, ⟨.and, [6,46]⟩, ⟨.or, [16,18]⟩, ⟨.or, [48,19]⟩, ⟨.or, [49,23]⟩, ⟨.and, [7,50]⟩, ⟨.or, [12,17]⟩, ⟨.or, [52,19]⟩, ⟨.or, [53,20]⟩, ⟨.and, [8,54]⟩, ⟨.or, [18,20]⟩, ⟨.or, [56,21]⟩, ⟨.and, [9,57]⟩, ⟨.or, [13,19]⟩, ⟨.or, [59,21]⟩, ⟨.or, [60,22]⟩, ⟨.and, [10,61]⟩, ⟨.or, [14,20]⟩, ⟨.or, [63,22]⟩, ⟨.or, [64,23]⟩, ⟨.and, [11,65]⟩, ⟨.or, [26,29]⟩, ⟨.or, [67,32]⟩, ⟨.or, [68,35]⟩, ⟨.or, [69,39]⟩, ⟨.or, [70,43]⟩, ⟨.or, [71,47]⟩, ⟨.or, [72,51]⟩, ⟨.or, [73,55]⟩, ⟨.or, [74,58]⟩, ⟨.or, [75,62]⟩, ⟨.or, [76,66]⟩],77⟩
def nearCircuitFn (x : Fin 24 → Bool) : Bool := (x 0 && x 12) || (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 12) || (x 2 && x 14) || (x 2 && x 18) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 12) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23)
theorem nearCircuit_size : nearCircuit.size = 54 := rfl
theorem nearCircuit_fan : FanInTwo nearCircuit := by simp [nearCircuit, FanInTwo]
theorem nearCircuit_eval (x : Fin 24 → Bool) : nearCircuit.eval (List.ofFn x) = nearCircuitFn x := by
  simp [nearCircuit, nearCircuitFn, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD, Bool.and_or_distrib_left, Bool.or_assoc]
theorem nearCircuit_bound : HasCircuitSize 24 nearCircuitFn 54 :=
  ⟨nearCircuit,nearCircuit_fan, Nat.le_of_eq nearCircuit_size,nearCircuit_eval⟩

theorem posted_reference : PEqualNP.MetaComplexity.HasCircuitSize 24 (fun x : Fin 24 → Bool => (x 0 && x 12) || (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 12) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 12) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23)) 55 := exactCircuit_bound
theorem omitted_edge (x : Fin 24 → Bool) : exactCircuitFn x = (nearCircuitFn x || (x 2 && x 13)) := by
  cases h : x 2 && x 13 <;> simp only [exactCircuitFn, nearCircuitFn, h, Bool.or_false, Bool.or_true, Bool.true_or]
#print axioms exactCircuit_size
#print axioms exactCircuit_fan
#print axioms exactCircuit_eval
#print axioms exactCircuit_bound
#print axioms nearCircuit_size
#print axioms nearCircuit_fan
#print axioms nearCircuit_eval
#print axioms nearCircuit_bound
#print axioms posted_reference
#print axioms omitted_edge
end PEqualNP.Research.Punctured24

import PEqualNP.Defs
import Mathlib.Tactic
import Std.Tactic.BVDecide
namespace PEqualNP.Research.IndependentTriple18872
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
def reference : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [35, 17]⟩, ⟨.and, [36, 18]⟩, ⟨.or, [0, 37]⟩, ⟨.and, [19, 20]⟩, ⟨.and, [39, 21]⟩, ⟨.or, [1, 40]⟩, ⟨.and, [25, 26]⟩, ⟨.and, [42, 27]⟩, ⟨.or, [5, 43]⟩, ⟨.and, [22, 28]⟩, ⟨.and, [45, 31]⟩, ⟨.and, [46, 34]⟩, ⟨.or, [12, 47]⟩, ⟨.and, [23, 29]⟩, ⟨.and, [49, 32]⟩, ⟨.or, [13, 50]⟩, ⟨.and, [24, 30]⟩, ⟨.and, [52, 33]⟩, ⟨.or, [14, 53]⟩, ⟨.and, [38, 41]⟩, ⟨.and, [55, 44]⟩, ⟨.and, [56, 48]⟩, ⟨.and, [57, 51]⟩, ⟨.and, [58, 54]⟩, ⟨.not, [59]⟩], 60⟩
theorem reference_fan : FanInTwo reference := by
  intro g hg
  simp [reference] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem reference_size : reference.size=46 := rfl
theorem reference_eval (x : Fin 15 → Bool) : reference.eval (List.ofFn x) = (!((((((x 0 || ((((x 1 || x 5) && (x 2 || x 6)) && (x 3 || x 7)) && (x 4 || x 8))) && (x 1 || (((x 2 || x 9) && (x 3 || x 10)) && (x 4 || x 11)))) && (x 5 || (((x 6 || x 9) && (x 7 || x 10)) && (x 8 || x 11)))) && (x 12 || ((((x 2 || x 3) && (x 6 || x 7)) && (x 9 || x 10)) && (x 13 || x 14)))) && (x 13 || (((x 2 || x 4) && (x 6 || x 8)) && (x 9 || x 11)))) && (x 14 || (((x 3 || x 4) && (x 7 || x 8)) && (x 10 || x 11))))) := by
  have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14] := rfl
  rw [hx]
  simp only [reference, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq, Bool.and_true, Bool.or_false, List.headD_cons]
def approximation : Circuit := ⟨[⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [33, 17]⟩, ⟨.or, [0, 34]⟩, ⟨.and, [18, 19]⟩, ⟨.and, [36, 20]⟩, ⟨.or, [1, 37]⟩, ⟨.and, [23, 24]⟩, ⟨.and, [39, 25]⟩, ⟨.or, [5, 40]⟩, ⟨.and, [26, 29]⟩, ⟨.and, [42, 32]⟩, ⟨.or, [12, 43]⟩, ⟨.and, [21, 27]⟩, ⟨.and, [45, 30]⟩, ⟨.or, [13, 46]⟩, ⟨.and, [22, 28]⟩, ⟨.and, [48, 31]⟩, ⟨.or, [14, 49]⟩, ⟨.and, [35, 38]⟩, ⟨.and, [51, 41]⟩, ⟨.and, [52, 44]⟩, ⟨.and, [53, 47]⟩, ⟨.and, [54, 50]⟩, ⟨.not, [55]⟩], 56⟩
theorem approximation_fan : FanInTwo approximation := by
  intro g hg
  simp [approximation] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem approximation_size : approximation.size=42 := rfl
theorem approximation_eval (x : Fin 15 → Bool) : approximation.eval (List.ofFn x) = (!((((((x 0 || (((x 2 || x 6) && (x 3 || x 7)) && (x 4 || x 8))) && (x 1 || (((x 2 || x 9) && (x 3 || x 10)) && (x 4 || x 11)))) && (x 5 || (((x 6 || x 9) && (x 7 || x 10)) && (x 8 || x 11)))) && (x 12 || (((x 6 || x 7) && (x 9 || x 10)) && (x 13 || x 14)))) && (x 13 || (((x 2 || x 4) && (x 6 || x 8)) && (x 9 || x 11)))) && (x 14 || (((x 3 || x 4) && (x 7 || x 8)) && (x 10 || x 11))))) := by
  have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14] := rfl
  rw [hx]
  simp only [approximation, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq, Bool.and_true, Bool.or_false, List.headD_cons]
def target : (Fin 15 → Bool) → Bool := (fun x : Fin 15 → Bool => (!(x 0) && !(x 1) && !(x 5)) || (!(x 0) && !(x 2) && !(x 6)) || (!(x 0) && !(x 3) && !(x 7)) || (!(x 0) && !(x 4) && !(x 8)) || (!(x 1) && !(x 2) && !(x 9)) || (!(x 1) && !(x 3) && !(x 10)) || (!(x 1) && !(x 4) && !(x 11)) || (!(x 2) && !(x 3) && !(x 12)) || (!(x 2) && !(x 4) && !(x 13)) || (!(x 3) && !(x 4) && !(x 14)) || (!(x 5) && !(x 6) && !(x 9)) || (!(x 5) && !(x 7) && !(x 10)) || (!(x 5) && !(x 8) && !(x 11)) || (!(x 6) && !(x 7) && !(x 12)) || (!(x 6) && !(x 8) && !(x 13)) || (!(x 7) && !(x 8) && !(x 14)) || (!(x 9) && !(x 10) && !(x 12)) || (!(x 9) && !(x 11) && !(x 13)) || (!(x 10) && !(x 11) && !(x 14)) || (!(x 12) && !(x 13) && !(x 14)))
theorem reference_correct (x : Fin 15 → Bool) : reference.eval (List.ofFn x) = target x := by
  rw [reference_eval];unfold target
  generalize h0 : x 0 = b0, h1 : x 1 = b1, h2 : x 2 = b2, h3 : x 3 = b3, h4 : x 4 = b4, h5 : x 5 = b5, h6 : x 6 = b6, h7 : x 7 = b7, h8 : x 8 = b8, h9 : x 9 = b9, h10 : x 10 = b10, h11 : x 11 = b11, h12 : x 12 = b12, h13 : x 13 = b13, h14 : x 14 = b14
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
theorem reference_bound : HasCircuitSize 15 target 46 := ⟨reference, reference_fan, reference_size.le, reference_correct⟩
def retained (x : Fin 15 → Bool) : Bool := (!(x 0) && !(x 2) && !(x 6)) || (!(x 0) && !(x 3) && !(x 7)) || (!(x 0) && !(x 4) && !(x 8)) || (!(x 1) && !(x 2) && !(x 9)) || (!(x 1) && !(x 3) && !(x 10)) || (!(x 1) && !(x 4) && !(x 11)) || (!(x 2) && !(x 4) && !(x 13)) || (!(x 3) && !(x 4) && !(x 14)) || (!(x 5) && !(x 6) && !(x 9)) || (!(x 5) && !(x 7) && !(x 10)) || (!(x 5) && !(x 8) && !(x 11)) || (!(x 6) && !(x 7) && !(x 12)) || (!(x 6) && !(x 8) && !(x 13)) || (!(x 7) && !(x 8) && !(x 14)) || (!(x 9) && !(x 10) && !(x 12)) || (!(x 9) && !(x 11) && !(x 13)) || (!(x 10) && !(x 11) && !(x 14)) || (!(x 12) && !(x 13) && !(x 14))
theorem approximation_correct (x : Fin 15 → Bool) : approximation.eval (List.ofFn x) = retained x := by
  rw [approximation_eval];unfold retained
  generalize h0 : x 0 = b0, h1 : x 1 = b1, h2 : x 2 = b2, h3 : x 3 = b3, h4 : x 4 = b4, h5 : x 5 = b5, h6 : x 6 = b6, h7 : x 7 = b7, h8 : x 8 = b8, h9 : x 9 = b9, h10 : x 10 = b10, h11 : x 11 = b11, h12 : x 12 = b12, h13 : x 13 = b13, h14 : x 14 = b14
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
theorem errors (x : Fin 15 → Bool) : target x = (approximation.eval (List.ofFn x) || (!(x 0) && !(x 1) && !(x 5)) || (!(x 2) && !(x 3) && !(x 12))) := by
  rw [approximation_correct];unfold target retained
  generalize h0 : x 0 = b0, h1 : x 1 = b1, h2 : x 2 = b2, h3 : x 3 = b3, h4 : x 4 = b4, h5 : x 5 = b5, h6 : x 6 = b6, h7 : x 7 = b7, h8 : x 8 = b8, h9 : x 9 = b9, h10 : x 10 = b10, h11 : x 11 = b11, h12 : x 12 = b12, h13 : x 13 = b13, h14 : x 14 = b14
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
end PEqualNP.Research.IndependentTriple18872

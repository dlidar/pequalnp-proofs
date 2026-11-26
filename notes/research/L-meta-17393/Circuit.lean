import FormulaMass
import PEqualNP.Defs
namespace PEqualNP.Research.Triangle17393
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Research.TripleFormulaMass
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
def triangle (x : Fin 10 → Bool) : Bool := (x 0 && x 1 && x 4) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 6) || (x 1 && x 2 && x 7) || (x 1 && x 3 && x 8) || (x 2 && x 3 && x 9) || (x 4 && x 5 && x 7) || (x 4 && x 6 && x 8) || (x 5 && x 6 && x 9) || (x 7 && x 8 && x 9)
def reference : Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [20, 12]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [4, 25]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [9, 28]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [30, 26]⟩, ⟨.or, [31, 29]⟩], 32⟩
theorem reference_fan : FanInTwo reference := by
  intro g hg
  simp [reference] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem reference_eval (x : Fin 10 → Bool) : reference.eval (List.ofFn x) = ((((x 0 && (((x 1 && x 4) || (x 2 && x 5)) || (x 3 && x 6))) || (x 1 && ((x 2 && x 7) || (x 3 && x 8)))) || (x 4 && ((x 5 && x 7) || (x 6 && x 8)))) || (x 9 && (((x 2 && x 3) || (x 5 && x 6)) || (x 7 && x 8)))) := by
  have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := rfl
  rw [hx]
  simp only [reference, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq, Bool.and_true, Bool.or_false, List.headD_cons]
def witness : Formula (Fin 10) := (.disj (.disj (.disj (.conj (.var 0) (.disj (.disj (.conj (.var 1) (.var 4)) (.conj (.var 2) (.var 5))) (.conj (.var 3) (.var 6)))) (.conj (.var 1) (.disj (.conj (.var 2) (.var 7)) (.conj (.var 3) (.var 8))))) (.conj (.var 4) (.disj (.conj (.var 5) (.var 7)) (.conj (.var 6) (.var 8))))) (.conj (.var 9) (.disj (.disj (.conj (.var 2) (.var 3)) (.conj (.var 5) (.var 6))) (.conj (.var 7) (.var 8)))))
theorem witness_size : witness.leaves=24 := rfl
theorem witness_eval (x : Fin 10 → Bool) : witness.eval x = reference.eval (List.ofFn x) := by rw [reference_eval];rfl
theorem reference_correct (x : Fin 10 → Bool) : reference.eval (List.ofFn x)=triangle x := by
  rw [reference_eval]; unfold triangle
  generalize h0 : x 0 = b0, h1 : x 1 = b1, h2 : x 2 = b2, h3 : x 3 = b3, h4 : x 4 = b4, h5 : x 5 = b5, h6 : x 6 = b6, h7 : x 7 = b7, h8 : x 8 = b8, h9 : x 9 = b9
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  decide +kernel
theorem upper_23 : HasCircuitSize 10 triangle 23 := ⟨reference,reference_fan,by decide +kernel,reference_correct⟩
end PEqualNP.Research.Triangle17393

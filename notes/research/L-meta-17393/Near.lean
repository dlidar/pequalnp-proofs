import Circuit
namespace PEqualNP.Research.Triangle17393
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds Finset
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
def near : Circuit := ⟨[⟨.not, [2]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 0]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [13, 6]⟩, ⟨.and, [13, 2]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [21, 16]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [4, 24]⟩, ⟨.or, [19, 20]⟩, ⟨.and, [12, 26]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [28, 27]⟩],29⟩
theorem near_counts : near.size=20 ∧ (near.gates.filter (fun g => match g.op with | .not => true | _ => false)).length=2 ∧ (near.gates.filter (fun g => match g.op with | .and => true | _ => false)).length=10 := by decide +kernel
theorem near_fan : FanInTwo near := by
  intro g hg
  simp [near] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def predNear (x : Fin 10 → Bool) := (((x 1 && (((x 4 && x 0) || (x 2 && x 7)) || (x 3 && x 8))) || (x 4 && ((x 7 && x 5) || (x 6 && x 8)))) || ((x 9 || x 0) && (((x 3 || x 5) && x 6) || ((x 3 || x 5) && x 2))))
theorem near_eval (x : Fin 10 → Bool) : near.eval (List.ofFn x)=predNear x := by
  unfold predNear
  have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := rfl
  rw [hx]
  simp only [near, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq, Bool.and_true, Bool.or_false, List.headD_cons]
def rowInput (r : Fin 1024) (i : Fin 10) := r.val.testBit i.val
theorem false_positive_count : (univ.filter (fun r : Fin 1024 => predNear (rowInput r) && !triangle (rowInput r))).card=36 := by decide +kernel
theorem false_negative_count : (univ.filter (fun r : Fin 1024 => triangle (rowInput r) && !predNear (rowInput r))).card=27 := by decide +kernel
end PEqualNP.Research.Triangle17393

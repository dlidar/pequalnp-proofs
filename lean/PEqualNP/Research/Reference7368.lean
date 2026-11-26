import PEqualNP.Defs

namespace PEqualNP.Research.Reference7368
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def ref : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.or,[24,3]⟩,
  ⟨.or,[15,16]⟩,
  ⟨.or,[26,18]⟩,
  ⟨.or,[12,14]⟩,
  ⟨.or,[28,20]⟩,
  ⟨.and,[0,29]⟩,
  ⟨.or,[13,19]⟩,
  ⟨.or,[31,23]⟩,
  ⟨.and,[1,32]⟩,
  ⟨.or,[12,18]⟩,
  ⟨.or,[34,22]⟩,
  ⟨.or,[35,23]⟩,
  ⟨.and,[2,36]⟩,
  ⟨.or,[17,21]⟩,
  ⟨.or,[38,22]⟩,
  ⟨.and,[3,39]⟩,
  ⟨.or,[16,20]⟩,
  ⟨.or,[41,21]⟩,
  ⟨.or,[42,23]⟩,
  ⟨.and,[4,43]⟩,
  ⟨.or,[15,19]⟩,
  ⟨.or,[45,20]⟩,
  ⟨.or,[46,22]⟩,
  ⟨.and,[5,47]⟩,
  ⟨.or,[14,18]⟩,
  ⟨.or,[49,19]⟩,
  ⟨.or,[50,21]⟩,
  ⟨.and,[6,51]⟩,
  ⟨.or,[13,17]⟩,
  ⟨.or,[53,18]⟩,
  ⟨.or,[54,20]⟩,
  ⟨.and,[7,55]⟩,
  ⟨.or,[12,16]⟩,
  ⟨.or,[57,17]⟩,
  ⟨.or,[58,19]⟩,
  ⟨.and,[8,59]⟩,
  ⟨.or,[14,15]⟩,
  ⟨.or,[61,17]⟩,
  ⟨.or,[62,23]⟩,
  ⟨.and,[9,63]⟩,
  ⟨.or,[13,14]⟩,
  ⟨.or,[65,16]⟩,
  ⟨.or,[66,22]⟩,
  ⟨.and,[10,67]⟩,
  ⟨.or,[12,13]⟩,
  ⟨.or,[69,15]⟩,
  ⟨.or,[70,21]⟩,
  ⟨.and,[11,71]⟩,
  ⟨.or,[30,33]⟩,
  ⟨.or,[73,37]⟩,
  ⟨.or,[74,40]⟩,
  ⟨.or,[75,44]⟩,
  ⟨.or,[76,48]⟩,
  ⟨.or,[77,52]⟩,
  ⟨.or,[78,56]⟩,
  ⟨.or,[79,60]⟩,
  ⟨.or,[80,64]⟩,
  ⟨.or,[81,68]⟩,
  ⟨.or,[82,72]⟩],83⟩
def flags : List (Fin 12 × Fin 12) := [(0,0), (0,2), (0,8), (1,1), (1,7), (1,11), (2,0), (2,6), (2,10), (2,11), (3,5), (3,9), (3,10), (4,4), (4,8), (4,9), (4,11), (5,3), (5,7), (5,8), (5,10), (6,2), (6,6), (6,7), (6,9), (7,1), (7,5), (7,6), (7,8), (8,0), (8,4), (8,5), (8,7), (9,2), (9,3), (9,5), (9,11), (10,1), (10,2), (10,4), (10,10), (11,0), (11,1), (11,3), (11,9)]

theorem incidence : ∀ p l : Fin 12, (p,l) ∈ flags ↔
    (9 : Fin 13).succAbove p + (0 : Fin 13).succAbove l ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide +kernel

def flagTest (x : Fin 24 → Bool) (f : Fin 12 × Fin 12) : Bool :=
  x (Fin.castAdd 12 f.1) && x (Fin.natAdd 12 f.2)

theorem read_flags (x : Fin 24 → Bool) : flags.any (flagTest x) = true ↔
    ∃ p l : Fin 12, (9 : Fin 13).succAbove p + (0 : Fin 13).succAbove l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
      x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 12 l) = true := by
  simp only [List.any_eq_true,flagTest,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,h,b⟩; exact ⟨p,l,(incidence ..).mp h,b⟩
  · rintro ⟨p,l,h,b⟩; exact ⟨(p,l),(incidence ..).mpr h,b⟩

theorem size : ref.size = 60 := rfl
theorem mono : Monotone2 ref := by
  let allowed := fun (g : Gate) =>
    (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
  have ok : ref.gates.all allowed = true := by decide +kernel
  intro g hg
  have test := List.all_eq_true.mp ok g hg
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [allowed]
theorem first : ref.gates.head? = some ⟨.or,[0,1]⟩ := rfl

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def bank24 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23]
private theorem init (x : Fin 24 → Bool) : List.ofFn x = bank24 x := by rfl
private def v24 (x : Fin 24 → Bool) := GateOp.eval .or [x 0, x 1]
private def bank25 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x]
private theorem s24 (x : Fin 24 → Bool) : step (bank24 x) ⟨.or, [0,1]⟩ = bank25 x := by rfl
private def v25 (x : Fin 24 → Bool) := GateOp.eval .or [v24 x, x 3]
private def bank26 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x]
private theorem s25 (x : Fin 24 → Bool) : step (bank25 x) ⟨.or, [24,3]⟩ = bank26 x := by rfl
private def v26 (x : Fin 24 → Bool) := GateOp.eval .or [x 15, x 16]
private def bank27 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x]
private theorem s26 (x : Fin 24 → Bool) : step (bank26 x) ⟨.or, [15,16]⟩ = bank27 x := by rfl
private def v27 (x : Fin 24 → Bool) := GateOp.eval .or [v26 x, x 18]
private def bank28 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x]
private theorem s27 (x : Fin 24 → Bool) : step (bank27 x) ⟨.or, [26,18]⟩ = bank28 x := by rfl
private def v28 (x : Fin 24 → Bool) := GateOp.eval .or [x 12, x 14]
private def bank29 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x]
private theorem s28 (x : Fin 24 → Bool) : step (bank28 x) ⟨.or, [12,14]⟩ = bank29 x := by rfl
private def v29 (x : Fin 24 → Bool) := GateOp.eval .or [v28 x, x 20]
private def bank30 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x]
private theorem s29 (x : Fin 24 → Bool) : step (bank29 x) ⟨.or, [28,20]⟩ = bank30 x := by rfl
private def v30 (x : Fin 24 → Bool) := GateOp.eval .and [x 0, v29 x]
private def bank31 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x]
private theorem s30 (x : Fin 24 → Bool) : step (bank30 x) ⟨.and, [0,29]⟩ = bank31 x := by rfl
private def v31 (x : Fin 24 → Bool) := GateOp.eval .or [x 13, x 19]
private def bank32 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x]
private theorem s31 (x : Fin 24 → Bool) : step (bank31 x) ⟨.or, [13,19]⟩ = bank32 x := by rfl
private def v32 (x : Fin 24 → Bool) := GateOp.eval .or [v31 x, x 23]
private def bank33 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x]
private theorem s32 (x : Fin 24 → Bool) : step (bank32 x) ⟨.or, [31,23]⟩ = bank33 x := by rfl
private def v33 (x : Fin 24 → Bool) := GateOp.eval .and [x 1, v32 x]
private def bank34 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]
private theorem s33 (x : Fin 24 → Bool) : step (bank33 x) ⟨.and, [1,32]⟩ = bank34 x := by rfl
private def v34 (x : Fin 24 → Bool) := GateOp.eval .or [x 12, x 18]
private def bank35 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x]
private theorem s34 (x : Fin 24 → Bool) : step (bank34 x) ⟨.or, [12,18]⟩ = bank35 x := by rfl
private def v35 (x : Fin 24 → Bool) := GateOp.eval .or [v34 x, x 22]
private def bank36 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x]
private theorem s35 (x : Fin 24 → Bool) : step (bank35 x) ⟨.or, [34,22]⟩ = bank36 x := by rfl
private def v36 (x : Fin 24 → Bool) := GateOp.eval .or [v35 x, x 23]
private def bank37 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x]
private theorem s36 (x : Fin 24 → Bool) : step (bank36 x) ⟨.or, [35,23]⟩ = bank37 x := by rfl
private def v37 (x : Fin 24 → Bool) := GateOp.eval .and [x 2, v36 x]
private def bank38 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]
private theorem s37 (x : Fin 24 → Bool) : step (bank37 x) ⟨.and, [2,36]⟩ = bank38 x := by rfl
private def v38 (x : Fin 24 → Bool) := GateOp.eval .or [x 17, x 21]
private def bank39 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x]
private theorem s38 (x : Fin 24 → Bool) : step (bank38 x) ⟨.or, [17,21]⟩ = bank39 x := by rfl
private def v39 (x : Fin 24 → Bool) := GateOp.eval .or [v38 x, x 22]
private def bank40 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x]
private theorem s39 (x : Fin 24 → Bool) : step (bank39 x) ⟨.or, [38,22]⟩ = bank40 x := by rfl
private def v40 (x : Fin 24 → Bool) := GateOp.eval .and [x 3, v39 x]
private def bank41 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x]
private theorem s40 (x : Fin 24 → Bool) : step (bank40 x) ⟨.and, [3,39]⟩ = bank41 x := by rfl
private def v41 (x : Fin 24 → Bool) := GateOp.eval .or [x 16, x 20]
private def bank42 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]
private theorem s41 (x : Fin 24 → Bool) : step (bank41 x) ⟨.or, [16,20]⟩ = bank42 x := by rfl
private def v42 (x : Fin 24 → Bool) := GateOp.eval .or [v41 x, x 21]
private def bank43 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x]
private theorem s42 (x : Fin 24 → Bool) : step (bank42 x) ⟨.or, [41,21]⟩ = bank43 x := by rfl
private def v43 (x : Fin 24 → Bool) := GateOp.eval .or [v42 x, x 23]
private def bank44 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x]
private theorem s43 (x : Fin 24 → Bool) : step (bank43 x) ⟨.or, [42,23]⟩ = bank44 x := by rfl
private def v44 (x : Fin 24 → Bool) := GateOp.eval .and [x 4, v43 x]
private def bank45 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x]
private theorem s44 (x : Fin 24 → Bool) : step (bank44 x) ⟨.and, [4,43]⟩ = bank45 x := by rfl
private def v45 (x : Fin 24 → Bool) := GateOp.eval .or [x 15, x 19]
private def bank46 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x]
private theorem s45 (x : Fin 24 → Bool) : step (bank45 x) ⟨.or, [15,19]⟩ = bank46 x := by rfl
private def v46 (x : Fin 24 → Bool) := GateOp.eval .or [v45 x, x 20]
private def bank47 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x]
private theorem s46 (x : Fin 24 → Bool) : step (bank46 x) ⟨.or, [45,20]⟩ = bank47 x := by rfl
private def v47 (x : Fin 24 → Bool) := GateOp.eval .or [v46 x, x 22]
private def bank48 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x]
private theorem s47 (x : Fin 24 → Bool) : step (bank47 x) ⟨.or, [46,22]⟩ = bank48 x := by rfl
private def v48 (x : Fin 24 → Bool) := GateOp.eval .and [x 5, v47 x]
private def bank49 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x]
private theorem s48 (x : Fin 24 → Bool) : step (bank48 x) ⟨.and, [5,47]⟩ = bank49 x := by rfl
private def v49 (x : Fin 24 → Bool) := GateOp.eval .or [x 14, x 18]
private def bank50 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x]
private theorem s49 (x : Fin 24 → Bool) : step (bank49 x) ⟨.or, [14,18]⟩ = bank50 x := by rfl
private def v50 (x : Fin 24 → Bool) := GateOp.eval .or [v49 x, x 19]
private def bank51 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x]
private theorem s50 (x : Fin 24 → Bool) : step (bank50 x) ⟨.or, [49,19]⟩ = bank51 x := by rfl
private def v51 (x : Fin 24 → Bool) := GateOp.eval .or [v50 x, x 21]
private def bank52 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x]
private theorem s51 (x : Fin 24 → Bool) : step (bank51 x) ⟨.or, [50,21]⟩ = bank52 x := by rfl
private def v52 (x : Fin 24 → Bool) := GateOp.eval .and [x 6, v51 x]
private def bank53 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x]
private theorem s52 (x : Fin 24 → Bool) : step (bank52 x) ⟨.and, [6,51]⟩ = bank53 x := by rfl
private def v53 (x : Fin 24 → Bool) := GateOp.eval .or [x 13, x 17]
private def bank54 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x]
private theorem s53 (x : Fin 24 → Bool) : step (bank53 x) ⟨.or, [13,17]⟩ = bank54 x := by rfl
private def v54 (x : Fin 24 → Bool) := GateOp.eval .or [v53 x, x 18]
private def bank55 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x]
private theorem s54 (x : Fin 24 → Bool) : step (bank54 x) ⟨.or, [53,18]⟩ = bank55 x := by rfl
private def v55 (x : Fin 24 → Bool) := GateOp.eval .or [v54 x, x 20]
private def bank56 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x]
private theorem s55 (x : Fin 24 → Bool) : step (bank55 x) ⟨.or, [54,20]⟩ = bank56 x := by rfl
private def v56 (x : Fin 24 → Bool) := GateOp.eval .and [x 7, v55 x]
private def bank57 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x]
private theorem s56 (x : Fin 24 → Bool) : step (bank56 x) ⟨.and, [7,55]⟩ = bank57 x := by rfl
private def v57 (x : Fin 24 → Bool) := GateOp.eval .or [x 12, x 16]
private def bank58 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x]
private theorem s57 (x : Fin 24 → Bool) : step (bank57 x) ⟨.or, [12,16]⟩ = bank58 x := by rfl
private def v58 (x : Fin 24 → Bool) := GateOp.eval .or [v57 x, x 17]
private def bank59 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x]
private theorem s58 (x : Fin 24 → Bool) : step (bank58 x) ⟨.or, [57,17]⟩ = bank59 x := by rfl
private def v59 (x : Fin 24 → Bool) := GateOp.eval .or [v58 x, x 19]
private def bank60 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x]
private theorem s59 (x : Fin 24 → Bool) : step (bank59 x) ⟨.or, [58,19]⟩ = bank60 x := by rfl
private def v60 (x : Fin 24 → Bool) := GateOp.eval .and [x 8, v59 x]
private def bank61 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x]
private theorem s60 (x : Fin 24 → Bool) : step (bank60 x) ⟨.and, [8,59]⟩ = bank61 x := by rfl
private def v61 (x : Fin 24 → Bool) := GateOp.eval .or [x 14, x 15]
private def bank62 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x]
private theorem s61 (x : Fin 24 → Bool) : step (bank61 x) ⟨.or, [14,15]⟩ = bank62 x := by rfl
private def v62 (x : Fin 24 → Bool) := GateOp.eval .or [v61 x, x 17]
private def bank63 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x]
private theorem s62 (x : Fin 24 → Bool) : step (bank62 x) ⟨.or, [61,17]⟩ = bank63 x := by rfl
private def v63 (x : Fin 24 → Bool) := GateOp.eval .or [v62 x, x 23]
private def bank64 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x]
private theorem s63 (x : Fin 24 → Bool) : step (bank63 x) ⟨.or, [62,23]⟩ = bank64 x := by rfl
private def v64 (x : Fin 24 → Bool) := GateOp.eval .and [x 9, v63 x]
private def bank65 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x]
private theorem s64 (x : Fin 24 → Bool) : step (bank64 x) ⟨.and, [9,63]⟩ = bank65 x := by rfl
private def v65 (x : Fin 24 → Bool) := GateOp.eval .or [x 13, x 14]
private def bank66 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x]
private theorem s65 (x : Fin 24 → Bool) : step (bank65 x) ⟨.or, [13,14]⟩ = bank66 x := by rfl
private def v66 (x : Fin 24 → Bool) := GateOp.eval .or [v65 x, x 16]
private def bank67 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x]
private theorem s66 (x : Fin 24 → Bool) : step (bank66 x) ⟨.or, [65,16]⟩ = bank67 x := by rfl
private def v67 (x : Fin 24 → Bool) := GateOp.eval .or [v66 x, x 22]
private def bank68 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x]
private theorem s67 (x : Fin 24 → Bool) : step (bank67 x) ⟨.or, [66,22]⟩ = bank68 x := by rfl
private def v68 (x : Fin 24 → Bool) := GateOp.eval .and [x 10, v67 x]
private def bank69 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x]
private theorem s68 (x : Fin 24 → Bool) : step (bank68 x) ⟨.and, [10,67]⟩ = bank69 x := by rfl
private def v69 (x : Fin 24 → Bool) := GateOp.eval .or [x 12, x 13]
private def bank70 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x]
private theorem s69 (x : Fin 24 → Bool) : step (bank69 x) ⟨.or, [12,13]⟩ = bank70 x := by rfl
private def v70 (x : Fin 24 → Bool) := GateOp.eval .or [v69 x, x 15]
private def bank71 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x]
private theorem s70 (x : Fin 24 → Bool) : step (bank70 x) ⟨.or, [69,15]⟩ = bank71 x := by rfl
private def v71 (x : Fin 24 → Bool) := GateOp.eval .or [v70 x, x 21]
private def bank72 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x]
private theorem s71 (x : Fin 24 → Bool) : step (bank71 x) ⟨.or, [70,21]⟩ = bank72 x := by rfl
private def v72 (x : Fin 24 → Bool) := GateOp.eval .and [x 11, v71 x]
private def bank73 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x]
private theorem s72 (x : Fin 24 → Bool) : step (bank72 x) ⟨.and, [11,71]⟩ = bank73 x := by rfl
private def v73 (x : Fin 24 → Bool) := GateOp.eval .or [v30 x, v33 x]
private def bank74 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x]
private theorem s73 (x : Fin 24 → Bool) : step (bank73 x) ⟨.or, [30,33]⟩ = bank74 x := by rfl
private def v74 (x : Fin 24 → Bool) := GateOp.eval .or [v73 x, v37 x]
private def bank75 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x]
private theorem s74 (x : Fin 24 → Bool) : step (bank74 x) ⟨.or, [73,37]⟩ = bank75 x := by rfl
private def v75 (x : Fin 24 → Bool) := GateOp.eval .or [v74 x, v40 x]
private def bank76 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x]
private theorem s75 (x : Fin 24 → Bool) : step (bank75 x) ⟨.or, [74,40]⟩ = bank76 x := by rfl
private def v76 (x : Fin 24 → Bool) := GateOp.eval .or [v75 x, v44 x]
private def bank77 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x]
private theorem s76 (x : Fin 24 → Bool) : step (bank76 x) ⟨.or, [75,44]⟩ = bank77 x := by rfl
private def v77 (x : Fin 24 → Bool) := GateOp.eval .or [v76 x, v48 x]
private def bank78 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x]
private theorem s77 (x : Fin 24 → Bool) : step (bank77 x) ⟨.or, [76,48]⟩ = bank78 x := by rfl
private def v78 (x : Fin 24 → Bool) := GateOp.eval .or [v77 x, v52 x]
private def bank79 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x]
private theorem s78 (x : Fin 24 → Bool) : step (bank78 x) ⟨.or, [77,52]⟩ = bank79 x := by rfl
private def v79 (x : Fin 24 → Bool) := GateOp.eval .or [v78 x, v56 x]
private def bank80 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x]
private theorem s79 (x : Fin 24 → Bool) : step (bank79 x) ⟨.or, [78,56]⟩ = bank80 x := by rfl
private def v80 (x : Fin 24 → Bool) := GateOp.eval .or [v79 x, v60 x]
private def bank81 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x]
private theorem s80 (x : Fin 24 → Bool) : step (bank80 x) ⟨.or, [79,60]⟩ = bank81 x := by rfl
private def v81 (x : Fin 24 → Bool) := GateOp.eval .or [v80 x, v64 x]
private def bank82 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x]
private theorem s81 (x : Fin 24 → Bool) : step (bank81 x) ⟨.or, [80,64]⟩ = bank82 x := by rfl
private def v82 (x : Fin 24 → Bool) := GateOp.eval .or [v81 x, v68 x]
private def bank83 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x]
private theorem s82 (x : Fin 24 → Bool) : step (bank82 x) ⟨.or, [81,68]⟩ = bank83 x := by rfl
private def v83 (x : Fin 24 → Bool) := GateOp.eval .or [v82 x, v72 x]
private def bank84 (x : Fin 24 → Bool) := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x]
private theorem s83 (x : Fin 24 → Bool) : step (bank83 x) ⟨.or, [82,72]⟩ = bank84 x := by rfl
theorem wires (x : Fin 24 → Bool) : ref.wires (List.ofFn x) = bank84 x := by
  change ref.gates.foldl step (List.ofFn x) = _
  simp only [ref, List.foldl_cons, List.foldl_nil, init, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83]
theorem left_marker (x : Fin 24 → Bool) : (ref.wires (List.ofFn x)).getD 25 false = (x 0 || x 1 || x 3) := by
  rw [wires]
  change v25 x = _
  simp [v25,v24, GateOp.eval]
theorem right_marker (x : Fin 24 → Bool) : (ref.wires (List.ofFn x)).getD 27 false = (x 15 || x 16 || x 18) := by
  rw [wires]
  change v27 x = _
  simp [v27,v26, GateOp.eval]
theorem output (x : Fin 24 → Bool) : ref.eval (List.ofFn x) = flags.any (flagTest x) := by
  change (ref.wires _).getD 83 false = _
  rw [wires]
  change v83 x = _
  have h : flags.any (flagTest x) = (((x 0) && (x 12)) || ((x 0) && (x 14)) || ((x 0) && (x 20)) || ((x 1) && (x 13)) || ((x 1) && (x 19)) || ((x 1) && (x 23)) || ((x 2) && (x 12)) || ((x 2) && (x 18)) || ((x 2) && (x 22)) || ((x 2) && (x 23)) || ((x 3) && (x 17)) || ((x 3) && (x 21)) || ((x 3) && (x 22)) || ((x 4) && (x 16)) || ((x 4) && (x 20)) || ((x 4) && (x 21)) || ((x 4) && (x 23)) || ((x 5) && (x 15)) || ((x 5) && (x 19)) || ((x 5) && (x 20)) || ((x 5) && (x 22)) || ((x 6) && (x 14)) || ((x 6) && (x 18)) || ((x 6) && (x 19)) || ((x 6) && (x 21)) || ((x 7) && (x 13)) || ((x 7) && (x 17)) || ((x 7) && (x 18)) || ((x 7) && (x 20)) || ((x 8) && (x 12)) || ((x 8) && (x 16)) || ((x 8) && (x 17)) || ((x 8) && (x 19)) || ((x 9) && (x 14)) || ((x 9) && (x 15)) || ((x 9) && (x 17)) || ((x 9) && (x 23)) || ((x 10) && (x 13)) || ((x 10) && (x 14)) || ((x 10) && (x 16)) || ((x 10) && (x 22)) || ((x 11) && (x 12)) || ((x 11) && (x 13)) || ((x 11) && (x 15)) || ((x 11) && (x 21))) := by
    simp only [flags, List.any_cons, List.any_nil, flagTest, Bool.or_false]
    change _ = _
    simp only [Bool.or_assoc]
    rfl
  rw [h]
  simp only [v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83,GateOp.eval,List.all_cons,List.any_cons,List.all_nil,List.any_nil,id_eq,Bool.and_true,Bool.or_false]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]

theorem exact_sixty : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 + x3 ∈ x1; have x3 : (Fin (24 : ℕ) → Bool) → Prop := fun (x3 : Fin (24 : ℕ) → Bool) => ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (12 : ℕ)), x2 (Fin.succAbove (9 : Fin (13 : ℕ)) x4) (Fin.succAbove (0 : Fin (13 : ℕ)) x5) ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (60 : ℕ) ∧ x4.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4.output < (24 : ℕ) + x4.size ∧ x5 < (24 : ℕ) + x4.size ∧ x6 < (24 : ℕ) + x4.size ∧ (∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.true ↔ x3 x7) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.false → (x4.wires (List.ofFn x7)).getD x5 Bool.false = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ (x4.wires (List.ofFn x7)).getD x6 Bool.false = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))) := by
  refine ⟨ref,25,27,mono,by decide +kernel,first,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩
  · intro x
    rw [output]
    exact read_flags x
  · exact fun x _ => ⟨left_marker x,right_marker x⟩

#print axioms incidence
#print axioms read_flags
#print axioms size
#print axioms mono
#print axioms first
#print axioms wires
#print axioms left_marker
#print axioms right_marker
#print axioms output
#print axioms exact_sixty
end PEqualNP.Research.Reference7368

import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask1885146376704737940Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [12, 11] },
  { op := GateOp.or, inputs := [13, 8] },
  { op := GateOp.or, inputs := [14, 9] },
  { op := GateOp.or, inputs := [14, 10] },
  { op := GateOp.or, inputs := [15, 10] },
  { op := GateOp.or, inputs := [16, 8] },
  { op := GateOp.or, inputs := [16, 9] },
  { op := GateOp.or, inputs := [17, 11] },
  { op := GateOp.or, inputs := [19, 8] },
  { op := GateOp.or, inputs := [18, 13] },
  { op := GateOp.or, inputs := [20, 12] },
  { op := GateOp.or, inputs := [20, 13] },
  { op := GateOp.or, inputs := [18, 15] },
  { op := GateOp.and, inputs := [0, 26] },
  { op := GateOp.and, inputs := [1, 28] },
  { op := GateOp.and, inputs := [2, 21] },
  { op := GateOp.and, inputs := [3, 24] },
  { op := GateOp.and, inputs := [4, 27] },
  { op := GateOp.and, inputs := [5, 25] },
  { op := GateOp.and, inputs := [6, 23] },
  { op := GateOp.and, inputs := [7, 22] },
  { op := GateOp.or, inputs := [29, 30] },
  { op := GateOp.or, inputs := [37, 31] },
  { op := GateOp.or, inputs := [38, 32] },
  { op := GateOp.or, inputs := [39, 33] },
  { op := GateOp.or, inputs := [40, 34] },
  { op := GateOp.or, inputs := [41, 35] },
  { op := GateOp.or, inputs := [42, 36] }], output := 43 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask1885146376704737940Upper_aux

theorem PEqualNP.Outside.Mask1885146376704737940Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.Mask1885146376704737940Upper_aux.upperC, PEqualNP.Outside.Mask1885146376704737940Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask1885146376704737940Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask1885146376704737940Upper

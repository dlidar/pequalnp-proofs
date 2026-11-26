import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14466700110149527140Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [11, 9] },
  { op := GateOp.or, inputs := [12, 8] },
  { op := GateOp.or, inputs := [13, 10] },
  { op := GateOp.or, inputs := [15, 14] },
  { op := GateOp.or, inputs := [16, 8] },
  { op := GateOp.or, inputs := [16, 12] },
  { op := GateOp.or, inputs := [18, 9] },
  { op := GateOp.or, inputs := [17, 13] },
  { op := GateOp.or, inputs := [18, 14] },
  { op := GateOp.or, inputs := [17, 15] },
  { op := GateOp.or, inputs := [19, 10] },
  { op := GateOp.or, inputs := [19, 11] },
  { op := GateOp.and, inputs := [0, 24] },
  { op := GateOp.and, inputs := [1, 22] },
  { op := GateOp.and, inputs := [2, 25] },
  { op := GateOp.and, inputs := [3, 23] },
  { op := GateOp.and, inputs := [4, 21] },
  { op := GateOp.and, inputs := [5, 20] },
  { op := GateOp.and, inputs := [6, 26] },
  { op := GateOp.and, inputs := [7, 27] },
  { op := GateOp.or, inputs := [28, 29] },
  { op := GateOp.or, inputs := [36, 30] },
  { op := GateOp.or, inputs := [37, 31] },
  { op := GateOp.or, inputs := [38, 32] },
  { op := GateOp.or, inputs := [39, 33] },
  { op := GateOp.or, inputs := [40, 34] },
  { op := GateOp.or, inputs := [41, 35] }], output := 42 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask14466700110149527140Upper_aux

theorem PEqualNP.Outside.Mask14466700110149527140Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  exact ⟨PEqualNP.Outside.Mask14466700110149527140Upper_aux.upperC, PEqualNP.Outside.Mask14466700110149527140Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask14466700110149527140Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask14466700110149527140Upper

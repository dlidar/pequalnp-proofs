import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14466700110149527140Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 14] },
  { op := GateOp.or, inputs := [16, 13] },
  { op := GateOp.or, inputs := [0, 14] },
  { op := GateOp.or, inputs := [17, 7] },
  { op := GateOp.or, inputs := [1, 15] },
  { op := GateOp.or, inputs := [2, 9] },
  { op := GateOp.or, inputs := [3, 11] },
  { op := GateOp.or, inputs := [4, 8] },
  { op := GateOp.or, inputs := [5, 12] },
  { op := GateOp.or, inputs := [18, 20] },
  { op := GateOp.or, inputs := [23, 24] },
  { op := GateOp.or, inputs := [19, 10] },
  { op := GateOp.or, inputs := [19, 26] },
  { op := GateOp.or, inputs := [20, 26] },
  { op := GateOp.or, inputs := [25, 10] },
  { op := GateOp.and, inputs := [24, 23] },
  { op := GateOp.and, inputs := [28, 22] },
  { op := GateOp.and, inputs := [29, 21] },
  { op := GateOp.and, inputs := [27, 25] },
  { op := GateOp.and, inputs := [30, 6] },
  { op := GateOp.or, inputs := [31, 32] },
  { op := GateOp.or, inputs := [36, 33] },
  { op := GateOp.or, inputs := [37, 34] },
  { op := GateOp.or, inputs := [38, 35] }], output := 39 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask14466700110149527140Upper_aux

theorem PEqualNP.Outside.Mask14466700110149527140Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  exact ⟨PEqualNP.Outside.Mask14466700110149527140Upper_aux.upperC, PEqualNP.Outside.Mask14466700110149527140Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask14466700110149527140Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask14466700110149527140Upper

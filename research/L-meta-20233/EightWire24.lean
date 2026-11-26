import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14466700110149527140Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 14] },
  { op := GateOp.or, inputs := [16, 10] },
  { op := GateOp.or, inputs := [0, 14] },
  { op := GateOp.and, inputs := [10, 6] },
  { op := GateOp.or, inputs := [19, 18] },
  { op := GateOp.or, inputs := [17, 6] },
  { op := GateOp.or, inputs := [1, 15] },
  { op := GateOp.or, inputs := [11, 3] },
  { op := GateOp.or, inputs := [2, 9] },
  { op := GateOp.or, inputs := [8, 4] },
  { op := GateOp.or, inputs := [5, 12] },
  { op := GateOp.or, inputs := [13, 7] },
  { op := GateOp.or, inputs := [20, 22] },
  { op := GateOp.or, inputs := [25, 26] },
  { op := GateOp.or, inputs := [21, 27] },
  { op := GateOp.or, inputs := [22, 29] },
  { op := GateOp.or, inputs := [29, 27] },
  { op := GateOp.and, inputs := [26, 25] },
  { op := GateOp.and, inputs := [31, 24] },
  { op := GateOp.and, inputs := [30, 28] },
  { op := GateOp.and, inputs := [32, 23] },
  { op := GateOp.or, inputs := [33, 34] },
  { op := GateOp.or, inputs := [37, 35] },
  { op := GateOp.or, inputs := [38, 36] }], output := 39 }

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

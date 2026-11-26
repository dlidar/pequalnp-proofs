import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14466700110149526116Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (14466700110149526116 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 15] },
  { op := GateOp.or, inputs := [2, 9] },
  { op := GateOp.or, inputs := [3, 11] },
  { op := GateOp.or, inputs := [4, 8] },
  { op := GateOp.or, inputs := [5, 12] },
  { op := GateOp.or, inputs := [7, 13] },
  { op := GateOp.or, inputs := [18, 17] },
  { op := GateOp.or, inputs := [20, 19] },
  { op := GateOp.or, inputs := [6, 0] },
  { op := GateOp.or, inputs := [14, 0] },
  { op := GateOp.or, inputs := [14, 10] },
  { op := GateOp.or, inputs := [6, 17] },
  { op := GateOp.or, inputs := [25, 18] },
  { op := GateOp.or, inputs := [28, 16] },
  { op := GateOp.and, inputs := [16, 27] },
  { op := GateOp.and, inputs := [22, 23] },
  { op := GateOp.and, inputs := [19, 20] },
  { op := GateOp.and, inputs := [24, 26] },
  { op := GateOp.and, inputs := [21, 29] },
  { op := GateOp.or, inputs := [30, 31] },
  { op := GateOp.or, inputs := [35, 32] },
  { op := GateOp.or, inputs := [36, 33] },
  { op := GateOp.or, inputs := [37, 34] }], output := 38 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask14466700110149526116Upper_aux

theorem PEqualNP.Outside.Mask14466700110149526116Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (14466700110149526116 : ℕ).testBit (8 * u.val + v.val)) 23 := by
  exact ⟨PEqualNP.Outside.Mask14466700110149526116Upper_aux.upperC, PEqualNP.Outside.Mask14466700110149526116Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask14466700110149526116Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask14466700110149526116Upper

theorem near_differences : ∀ i j : Fin 8, (14466700110149526116 : Nat).testBit (8*i.val+j.val) ≠ (14466700110149527140 : Nat).testBit (8*i.val+j.val) ↔ (i=1 ∧ j=2) := by decide +kernel
#print axioms near_differences

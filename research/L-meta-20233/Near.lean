import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14465574209697424996Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (14465574209697424996 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [3, 2] },
  { op := GateOp.or, inputs := [5, 4] },
  { op := GateOp.or, inputs := [7, 6] },
  { op := GateOp.or, inputs := [13, 10] },
  { op := GateOp.or, inputs := [15, 14] },
  { op := GateOp.or, inputs := [16, 4] },
  { op := GateOp.or, inputs := [16, 5] },
  { op := GateOp.or, inputs := [17, 1] },
  { op := GateOp.or, inputs := [17, 7] },
  { op := GateOp.or, inputs := [19, 14] },
  { op := GateOp.and, inputs := [0, 25] },
  { op := GateOp.and, inputs := [1, 19] },
  { op := GateOp.and, inputs := [21, 12] },
  { op := GateOp.and, inputs := [22, 8] },
  { op := GateOp.and, inputs := [23, 9] },
  { op := GateOp.and, inputs := [24, 11] },
  { op := GateOp.and, inputs := [18, 20] },
  { op := GateOp.or, inputs := [26, 27] },
  { op := GateOp.or, inputs := [33, 28] },
  { op := GateOp.or, inputs := [34, 29] },
  { op := GateOp.or, inputs := [35, 30] },
  { op := GateOp.or, inputs := [36, 31] },
  { op := GateOp.or, inputs := [37, 32] }], output := 38 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask14465574209697424996Upper_aux

theorem PEqualNP.Outside.Mask14465574209697424996Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (14465574209697424996 : ℕ).testBit (8 * u.val + v.val)) 23 := by
  exact ⟨PEqualNP.Outside.Mask14465574209697424996Upper_aux.upperC, PEqualNP.Outside.Mask14465574209697424996Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask14465574209697424996Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask14465574209697424996Upper

theorem near_differences : ∀ i j : Fin 8, (14465574209697424996 : Nat).testBit (8*i.val+j.val) ≠ (14466700110149527140 : Nat).testBit (8*i.val+j.val) ↔ (i=2 ∧ j=7) ∨ (i=3 ∧ j=5) ∨ (i=6 ∧ j=2) := by decide +kernel
#print axioms near_differences

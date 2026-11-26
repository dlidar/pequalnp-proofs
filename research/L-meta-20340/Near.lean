import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask1164570436325425812Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 8 → Fin 8 → Bool := fun (u : Fin 8) (v : Fin 8) => (1164570436325425812 : ℕ).testBit (8 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [4, 0] },
  { op := GateOp.or, inputs := [5, 1] },
  { op := GateOp.or, inputs := [6, 2] },
  { op := GateOp.or, inputs := [6, 5] },
  { op := GateOp.or, inputs := [7, 2] },
  { op := GateOp.or, inputs := [11, 8] },
  { op := GateOp.or, inputs := [14, 9] },
  { op := GateOp.or, inputs := [14, 10] },
  { op := GateOp.or, inputs := [15, 10] },
  { op := GateOp.or, inputs := [19, 4] },
  { op := GateOp.or, inputs := [20, 0] },
  { op := GateOp.or, inputs := [23, 8] },
  { op := GateOp.and, inputs := [3, 27] },
  { op := GateOp.and, inputs := [16, 24] },
  { op := GateOp.and, inputs := [17, 22] },
  { op := GateOp.and, inputs := [18, 21] },
  { op := GateOp.and, inputs := [25, 13] },
  { op := GateOp.and, inputs := [26, 12] },
  { op := GateOp.or, inputs := [28, 29] },
  { op := GateOp.or, inputs := [34, 30] },
  { op := GateOp.or, inputs := [35, 31] },
  { op := GateOp.or, inputs := [36, 32] },
  { op := GateOp.or, inputs := [37, 33] }], output := 38 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask1164570436325425812Upper_aux

theorem PEqualNP.Outside.Mask1164570436325425812Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 8) => (1164570436325425812 : ℕ).testBit (8 * u.val + v.val)) 23 := by
  exact ⟨PEqualNP.Outside.Mask1164570436325425812Upper_aux.upperC, PEqualNP.Outside.Mask1164570436325425812Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask1164570436325425812Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask1164570436325425812Upper

theorem near_differences : ∀ i j : Fin 8, (1164570436325425812 : Nat).testBit (8*i.val+j.val) ≠ (1885146376704737940 : Nat).testBit (8*i.val+j.val) ↔ (i=1 ∧ j=7) ∨ (i=7 ∧ (j=1 ∨ j=3)) := by decide +kernel
#print axioms near_differences

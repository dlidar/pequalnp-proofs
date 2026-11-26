import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask1227Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 5 → Bool := fun (u : Fin 3) (v : Fin 5) => (1227 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [6, 4] },
      { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [10, 1] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.or, inputs := [11, 3] },
      { op := GateOp.or, inputs := [12, 2] },
      { op := GateOp.and, inputs := [13, 14] }], output := 15 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask1227Upper_aux

theorem PEqualNP.Outside.Mask1227Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1227 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.Mask1227Upper_aux.upperC, PEqualNP.Outside.Mask1227Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask1227Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask1227Upper

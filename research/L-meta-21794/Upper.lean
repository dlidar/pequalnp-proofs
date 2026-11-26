import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask272255Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (272255 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [6, 7] },
      { op := GateOp.or, inputs := [10, 8] },
      { op := GateOp.and, inputs := [11, 1] },
      { op := GateOp.or, inputs := [0, 12] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.or, inputs := [14, 3] },
      { op := GateOp.and, inputs := [15, 16] },
      { op := GateOp.or, inputs := [13, 17] }], output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask272255Upper_aux

theorem PEqualNP.Outside.Mask272255Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272255 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨PEqualNP.Outside.Mask272255Upper_aux.upperC, PEqualNP.Outside.Mask272255Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask272255Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask272255Upper

import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask106301Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (106301 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.or, inputs := [0, 2] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.and, inputs := [11, 9] },
      { op := GateOp.or, inputs := [12, 4] },
      { op := GateOp.and, inputs := [6, 10] },
      { op := GateOp.or, inputs := [14, 13] },
      { op := GateOp.or, inputs := [2, 3] },
      { op := GateOp.and, inputs := [5, 16] },
      { op := GateOp.or, inputs := [15, 17] }], output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask106301Upper_aux

theorem PEqualNP.Outside.Mask106301Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106301 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.Mask106301Upper_aux.upperC, PEqualNP.Outside.Mask106301Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask106301Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask106301Upper

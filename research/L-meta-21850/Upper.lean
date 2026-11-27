import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask292607Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (292607 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [11, 5] },
      { op := GateOp.and, inputs := [1, 12] },
      { op := GateOp.or, inputs := [13, 10] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [15, 2] },
      { op := GateOp.or, inputs := [16, 14] }], output := 17 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask292607Upper_aux

theorem PEqualNP.Outside.Mask292607Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292607 : ℕ).testBit (6 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.Mask292607Upper_aux.upperC, PEqualNP.Outside.Mask292607Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask292607Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask292607Upper

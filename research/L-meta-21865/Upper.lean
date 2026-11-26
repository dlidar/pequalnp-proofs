import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask323518Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (323518 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.and, inputs := [11, 10] },
      { op := GateOp.or, inputs := [12, 5] },
      { op := GateOp.or, inputs := [10, 2] },
      { op := GateOp.or, inputs := [13, 6] },
      { op := GateOp.or, inputs := [15, 7] },
      { op := GateOp.and, inputs := [14, 16] },
      { op := GateOp.and, inputs := [4, 3] },
      { op := GateOp.or, inputs := [17, 18] }], output := 19 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask323518Upper_aux

theorem PEqualNP.Outside.Mask323518Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323518 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.Mask323518Upper_aux.upperC, PEqualNP.Outside.Mask323518Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask323518Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask323518Upper

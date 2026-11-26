import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask386990Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (386990 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [9, 3] },
      { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.or, inputs := [13, 7] },
      { op := GateOp.or, inputs := [14, 8] },
      { op := GateOp.or, inputs := [14, 10] },
      { op := GateOp.and, inputs := [12, 15] },
      { op := GateOp.and, inputs := [11, 16] },
      { op := GateOp.or, inputs := [17, 18] }], output := 19 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask386990Upper_aux

theorem PEqualNP.Outside.Mask386990Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (386990 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.Mask386990Upper_aux.upperC, PEqualNP.Outside.Mask386990Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask386990Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask386990Upper

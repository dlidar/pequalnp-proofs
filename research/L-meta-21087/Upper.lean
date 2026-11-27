import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask114591Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [8, 1] },
      { op := GateOp.or, inputs := [0, 9] },
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 7] },
      { op := GateOp.and, inputs := [12, 11] },
      { op := GateOp.or, inputs := [10, 13] },
      { op := GateOp.or, inputs := [2, 3] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [16, 15] },
      { op := GateOp.or, inputs := [14, 17] }], output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask114591Upper_aux

theorem PEqualNP.Outside.Mask114591Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.Mask114591Upper_aux.upperC, PEqualNP.Outside.Mask114591Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask114591Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask114591Upper

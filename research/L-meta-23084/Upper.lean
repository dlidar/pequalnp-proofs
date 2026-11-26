import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask14124Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 6 → Bool := fun (u : Fin 3) (v : Fin 6) => (14124 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [8, 2] },
      { op := GateOp.or, inputs := [0, 3] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.or, inputs := [11, 7] },
      { op := GateOp.or, inputs := [11, 9] },
      { op := GateOp.and, inputs := [1, 12] },
      { op := GateOp.or, inputs := [10, 4] },
      { op := GateOp.and, inputs := [15, 13] },
      { op := GateOp.or, inputs := [14, 16] }], output := 17 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask14124Upper_aux

theorem PEqualNP.Outside.Mask14124Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14124 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨PEqualNP.Outside.Mask14124Upper_aux.upperC, PEqualNP.Outside.Mask14124Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask14124Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask14124Upper

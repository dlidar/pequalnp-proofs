import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Mask1534Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 5 → Bool := fun (u : Fin 3) (v : Fin 5) => (1534 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.or, inputs := [8, 6] },
      { op := GateOp.or, inputs := [9, 7] },
      { op := GateOp.and, inputs := [0, 10] },
      { op := GateOp.and, inputs := [1, 9] },
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 13] },
      { op := GateOp.or, inputs := [11, 12] },
      { op := GateOp.or, inputs := [14, 15] }],
    output := 16 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask1534Upper_aux

theorem PEqualNP.Outside.Mask1534Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1534 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨PEqualNP.Outside.Mask1534Upper_aux.upperC, PEqualNP.Outside.Mask1534Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask1534Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask1534Upper

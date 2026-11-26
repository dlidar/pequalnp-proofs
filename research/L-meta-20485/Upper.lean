import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask1259Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 5 → Bool := fun (u : Fin 3) (v : Fin 5) => (1259 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [8, 1] },
      { op := GateOp.or, inputs := [9, 3] },
      { op := GateOp.or, inputs := [4, 6] },
      { op := GateOp.and, inputs := [11, 0] },
      { op := GateOp.or, inputs := [12, 10] }], output := 13 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask1259Upper_aux

theorem PEqualNP.Outside.Mask1259Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1259 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  exact ⟨PEqualNP.Outside.Mask1259Upper_aux.upperC, PEqualNP.Outside.Mask1259Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask1259Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask1259Upper

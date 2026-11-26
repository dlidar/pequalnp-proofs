import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask245567Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (245567 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.and, inputs := [8, 1] },
      { op := GateOp.or, inputs := [10, 7] },
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [11, 12] },
      { op := GateOp.or, inputs := [13, 9] },
      { op := GateOp.or, inputs := [2, 3] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [16, 15] },
      { op := GateOp.or, inputs := [14, 17] }], output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask245567Upper_aux

theorem PEqualNP.Outside.Mask245567Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245567 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.Mask245567Upper_aux.upperC, PEqualNP.Outside.Mask245567Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask245567Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask245567Upper

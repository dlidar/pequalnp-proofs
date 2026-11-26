import Mathlib
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Mask815863Upper_aux

-- The explicit witness is evaluated on every promised row and column.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (815863 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.and, inputs := [10, 0] },
      { op := GateOp.or, inputs := [11, 1] },
      { op := GateOp.or, inputs := [0, 7] },
      { op := GateOp.or, inputs := [13, 2] },
      { op := GateOp.or, inputs := [12, 6] },
      { op := GateOp.and, inputs := [15, 14] },
      { op := GateOp.or, inputs := [16, 4] },
      { op := GateOp.or, inputs := [17, 5] }], output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.Mask815863Upper_aux

theorem PEqualNP.Outside.Mask815863Upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815863 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨PEqualNP.Outside.Mask815863Upper_aux.upperC, PEqualNP.Outside.Mask815863Upper_aux.upper_mono, by decide, PEqualNP.Outside.Mask815863Upper_aux.upper_rep⟩

#print axioms PEqualNP.Outside.Mask815863Upper

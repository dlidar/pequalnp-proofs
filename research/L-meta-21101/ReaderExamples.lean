import Mathlib
import PEqualNP.Defs.Represents

namespace Mask245567Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A (u : Fin 4) (v : Fin 5) : Bool := (245567 : Nat).testBit (5*u.val+v.val)

def countRead (c : Circuit) (wire : Nat) : Nat :=
  (c.gates.flatMap (fun g => g.inputs)).count wire

def c0 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩
theorem profile0 : Monotone2 c0 ∧ c0.size = 10 ∧ PEqualNP.Represents.Represents A c0 ∧ (List.range 18).map (countRead c0) = [1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c0] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def c1 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩
theorem profile1 : Monotone2 c1 ∧ c1.size = 10 ∧ PEqualNP.Represents.Represents A c1 ∧ (List.range 18).map (countRead c1) = [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c1] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def c2 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [12, 17]⟩], 18⟩
theorem profile2 : Monotone2 c2 ∧ c2.size = 10 ∧ PEqualNP.Represents.Represents A c2 ∧ (List.range 18).map (countRead c2) = [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c2] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def c3 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩
theorem profile3 : Monotone2 c3 ∧ c3.size = 10 ∧ PEqualNP.Represents.Represents A c3 ∧ (List.range 18).map (countRead c3) = [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c3] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def c4 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [17, 16]⟩], 18⟩
theorem profile4 : Monotone2 c4 ∧ c4.size = 10 ∧ PEqualNP.Represents.Represents A c4 ∧ (List.range 18).map (countRead c4) = [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c4] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
def c5 : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩
theorem profile5 : Monotone2 c5 ∧ c5.size = 10 ∧ PEqualNP.Represents.Represents A c5 ∧ (List.range 18).map (countRead c5) = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1] := by
  refine ⟨?_, by decide, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [c5] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask245567Readers
#print axioms Mask245567Readers.profile0
#print axioms Mask245567Readers.profile1
#print axioms Mask245567Readers.profile2
#print axioms Mask245567Readers.profile3
#print axioms Mask245567Readers.profile4
#print axioms Mask245567Readers.profile5

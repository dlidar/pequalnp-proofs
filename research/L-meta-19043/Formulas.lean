import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask5805Formulas
def graph (u v : Fin 4) := (5805 : Nat).testBit (4*u.val+v.val)
def monotoneTree : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [4, 13]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [8, 17]⟩], 18⟩
theorem monotoneTree_correct : PEqualNP.Represents.Represents graph monotoneTree := by decide +kernel
theorem monotoneTree_size : monotoneTree.size = 11 := by decide
theorem monotoneTree_fanin : FanInTwo monotoneTree := by
  intro g hg
  simp [monotoneTree] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
#print axioms monotoneTree_correct
#print axioms monotoneTree_size
#print axioms monotoneTree_fanin
def unrestrictedTree : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [8, 16]⟩], 17⟩
theorem unrestrictedTree_correct : PEqualNP.Represents.Represents graph unrestrictedTree := by decide +kernel
theorem unrestrictedTree_size : unrestrictedTree.size = 10 := by decide
theorem unrestrictedTree_fanin : FanInTwo unrestrictedTree := by
  intro g hg
  simp [unrestrictedTree] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
#print axioms unrestrictedTree_correct
#print axioms unrestrictedTree_size
#print axioms unrestrictedTree_fanin
end Mask5805Formulas

import PEqualNP.Defs
import PEqualNP.Defs.Represents

namespace PEqualNP.Research.L_meta_10144

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Wires 10 and 11 collect the two pairs of twin vertices. Wire 12 is used twice. -/
def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 6]⟩,
    ⟨.or, [1, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [13, 14]⟩,
    ⟨.or, [10, 9]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [2, 17]⟩,
    ⟨.and, [16, 18]⟩, ⟨.or, [15, 19]⟩], 20⟩

theorem witness_monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_correct : Represents
    (fun u v : Fin 5 => (3260881 : ℕ).testBit (5 * u.val + v.val)) witness := by decide +kernel

theorem upper : RepSizeAtMost
    (fun u v : Fin 5 => (3260881 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨witness, witness_monotone, by decide, witness_correct⟩

#print axioms upper
end PEqualNP.Research.L_meta_10144

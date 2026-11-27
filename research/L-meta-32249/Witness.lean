import Graph
namespace Graph32249
open PEqualNP.Research.TripleFormulaMass
def treeWitness : Formula (Fin 8) := (.disj (.conj (.var 5) (.var 7)) (.disj (.conj (.var 6) (.disj (.var 2) (.var 4))) (.disj (.conj (.disj (.var 3) (.disj (.var 0) (.var 2))) (.disj (.var 5) (.var 7))) (.disj (.conj (.var 0) (.var 3)) (.conj (.disj (.var 0) (.var 1)) (.disj (.var 4) (.var 6)))))))
theorem tree_size : treeWitness.leaves=16 := rfl
theorem tree_correct : ∀ x, treeWitness.eval x=target x := by decide +kernel
end Graph32249

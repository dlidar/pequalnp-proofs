import Graph
namespace Graph29313
open PEqualNP.Research.TripleFormulaMass
def treeWitness : Formula (Fin 8) := (.disj (.conj (.var 7) (.disj (.var 4) (.disj (.var 1) (.var 3)))) (.disj (.conj (.disj (.var 2) (.var 6)) (.disj (.var 5) (.var 7))) (.disj (.conj (.var 4) (.disj (.var 0) (.var 6))) (.conj (.disj (.var 0) (.var 1)) (.disj (.var 5) (.var 6))))))
theorem tree_size : treeWitness.leaves=15 := rfl
theorem tree_correct : ∀ x, treeWitness.eval x=target x := by decide +kernel
end Graph29313

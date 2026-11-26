import Final
import AxiomOverlap
namespace PHPOverlap
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph
theorem necessary_sharing (π : List (LinClause Grid)) (refute : IsLinRefutation (PHP 4 3) π) (short : π.length ≤ 51) :
    ∃ C P r c d, Encoded F C P π ∧ r < π.length ∧ P r = [c,d] ∧ c ≠ d ∧
      (∀ a, FalseAt C a r) ∧ 10 ≤ (Live P c ∩ Live P d).card ∧
      6 ≤ (WithArity P c 0 ∩ WithArity P d 0).card ∧
      10 + (WithArity P r 1).card + Surplus P r ≤ 2*(WithArity P c 0 ∩ WithArity P d 0).card :=
  both_counts every_root π refute short
#print axioms necessary_sharing
end PHPOverlap

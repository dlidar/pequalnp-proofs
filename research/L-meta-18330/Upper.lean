import CachedBase
namespace PEqualNP.Research.Cached18330
open TripleFormulaMass
set_option maxRecDepth 16000
def ordinary : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.disj (.disj (.var (some 0)) (.var (some 1))) (.var (some 3))) (.var (some 7))) (.conj (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4))) (.var (some 8)))) (.conj (.disj (.disj (.var (some 2)) (.var (some 3))) (.var (some 5))) (.var (some 9)))) (.conj (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))) (.var (some 10)))) (.conj (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))) (.var (some 11)))) (.conj (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))) (.var (some 12)))) (.conj (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))) (.var (some 13))))
theorem ordinarySize : ordinary.leaves = 28 := by decide +kernel
theorem ordinaryEval (k : Key) (x : EdgeInput → Bool) : ordinary.eval (extendsKey k x) = target x := by
  change (((((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) || (((x 0 || x 4) || x 5) && x 11)) || (((x 1 || x 5) || x 6) && x 12)) || (((x 0 || x 2) || x 6) && x 13)) = ((x 0 && x 7) || ((x 0 && x 11) || ((x 0 && x 13) || ((x 1 && x 7) || ((x 1 && x 8) || ((x 1 && x 12) || ((x 2 && x 8) || ((x 2 && x 9) || ((x 2 && x 13) || ((x 3 && x 7) || ((x 3 && x 9) || ((x 3 && x 10) || ((x 4 && x 8) || ((x 4 && x 10) || ((x 4 && x 11) || ((x 5 && x 9) || ((x 5 && x 11) || ((x 5 && x 12) || ((x 6 && x 10) || ((x 6 && x 12) || ((x 6 && x 13) || false)))))))))))))))))))))
  simp only [Bool.and_or_distrib_right,Bool.or_false]
  ac_rfl
def pairOr : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.disj (.var none) (.var (some 3))) (.var (some 7))) (.conj (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4))) (.var (some 8)))) (.conj (.disj (.disj (.var (some 2)) (.var (some 3))) (.var (some 5))) (.var (some 9)))) (.conj (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))) (.var (some 10)))) (.conj (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))) (.var (some 11)))) (.conj (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))) (.var (some 12)))) (.conj (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))) (.var (some 13))))
theorem pairOrSize : pairOr.leaves = 27 := by decide +kernel
theorem pairOrEval (x : EdgeInput → Bool) : pairOr.eval (extendsKey 91 x) = target x := by
  change (((((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) || (((x 0 || x 4) || x 5) && x 11)) || (((x 1 || x 5) || x 6) && x 12)) || (((x 0 || x 2) || x 6) && x 13)) = ((x 0 && x 7) || ((x 0 && x 11) || ((x 0 && x 13) || ((x 1 && x 7) || ((x 1 && x 8) || ((x 1 && x 12) || ((x 2 && x 8) || ((x 2 && x 9) || ((x 2 && x 13) || ((x 3 && x 7) || ((x 3 && x 9) || ((x 3 && x 10) || ((x 4 && x 8) || ((x 4 && x 10) || ((x 4 && x 11) || ((x 5 && x 9) || ((x 5 && x 11) || ((x 5 && x 12) || ((x 6 && x 10) || ((x 6 && x 12) || ((x 6 && x 13) || false)))))))))))))))))))))
  simp only [Bool.and_or_distrib_right,Bool.or_false]
  ac_rfl
end PEqualNP.Research.Cached18330

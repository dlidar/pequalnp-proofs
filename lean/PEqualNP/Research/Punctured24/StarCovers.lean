import Mathlib.Tactic
namespace PEqualNP.Research.StarCover24
set_option maxRecDepth 65536
set_option maxHeartbeats 0
-- A zero left bit marks an omitted point. Every adjacent line must be selected.
def forcedAux : List Nat → Nat → Nat
  | [], _ => 0
  | r :: rs, x => (if x % 2 = 0 then r else 0) ||| forcedAux rs (x / 2)
def forced := forcedAux [1041, 2082, 71, 140, 282, 564, 1128, 2256, 417, 832, 1666, 3332]
def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x => x % 2 + countBits n (x / 2)
def tightWeight (x : Nat) := countBits 12 x + countBits 12 (forced x)
def masks := List.range 4096
-- Fixing the left half of a cover, the forced lines give its unique
-- inclusion-minimal right half.
theorem minimum : (masks.map tightWeight).min? = some 12 := by decide +kernel
theorem pure_minimizers : masks.filter (fun x => tightWeight x == 12) = [0,4095] := by decide +kernel
def mixed := masks.filter fun x => x != 4095 && forced x != 4095
theorem mixed_minimum : (mixed.map tightWeight).min? = some 14 := by decide +kernel
theorem mixed_minimizers : ((mixed.filter (fun x => tightWeight x == 14)).map (fun x => (x,forced x))) = [(88,4087), (261,4094), (1568,3583), (2178,2047), (3583,832), (4087,140), (4093,2082), (4094,1041)] := by decide +kernel
#print axioms minimum
#print axioms pure_minimizers
#print axioms mixed_minimum
#print axioms mixed_minimizers
end PEqualNP.Research.StarCover24

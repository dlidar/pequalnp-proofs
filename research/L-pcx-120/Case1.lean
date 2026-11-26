import GridPacks
namespace PHPOverlap
open PEqualNP.Outside.L_pcx_118.Graph
def pack1_0 : List Nat := [266, 2058, 610, 2114, 778, 660, 2184, 2186, 1124, 2130, 1292, 802, 2122, 1108, 1290, 1164, 2188, 2146, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1_0 : checkPack 1 false pack1_0 = true := by decide +kernel
def pack1_1 : List Nat := [273, 785, 2065, 2129, 1185, 2177, 2185, 1297, 1313, 2193, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1_1 : checkPack 1 true pack1_1 = true := by decide +kernel
theorem bound1 {C : ClauseMap Grid} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hc : c < r) (hd : d < r)
    (side : ∀ a : Grid → Bool, if Odd (((form 1).filter (fun v => a v = true)).card) then FalseAt C a d else FalseAt C a c) :
    62 ≤ r + (Live P c ∩ Live P d).card + 2 := by
  have h0 := half_count (fun i hi => rules i (hi.trans hc.le)) (r := c) (m := 1) (b := false) (xs := pack1_0) (by
    intro a h
    have ss := side a
    split at ss <;> simp_all) checked1_0
  have h1 := half_count (fun i hi => rules i (hi.trans hd.le)) (r := d) (m := 1) (b := true) (xs := pack1_1) (by
    intro a h
    have ss := side a
    split at ss <;> simp_all) checked1_1
  exact overlap_bound rules hc hd h0 h1
end PHPOverlap
#print axioms PHPOverlap.bound1

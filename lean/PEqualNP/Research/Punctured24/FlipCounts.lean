import Mathlib.Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PEqualNP.Research.Punctured24
/- The number of independent sets remaining after forcing two endpoints on
and forcing all their other neighbors off. Each available point can be
omitted, or selected at the cost of removing its adjacent available lines. -/
def lineWays : Nat → Nat → Nat
  | 0, _ => 1
  | n+1, m => (1 + m % 2) * lineWays n (m / 2)

def ways : List Nat → Nat → Nat
  | [], m => lineWays 12 m
  | r :: rs, m => ways rs m + ways rs (m ^^^ (m &&& r))

def rows : List Nat := [1041, 2082, 71, 140, 282, 564, 1128, 2256, 417, 832, 1666, 3332]
def adj (a b : Nat) : Bool :=
  if a < 12 ∧ 12 ≤ b then (rows[a]!).testBit (b-12)
  else if b < 12 ∧ 12 ≤ a then (rows[b]!).testBit (a-12)
  else false

def freeAt (a b v : Nat) : Bool :=
  v != a && v != b && !adj a v && !adj b v

def flipCount (a b : Nat) : Nat :=
  let pts := (List.range 12).filter (freeAt a b)
  let lines := (List.range 12).foldl (fun m j =>
    if freeAt a b (j+12) then m + 2^j else m) 0
  ways (pts.map fun i => rows[i]!) lines

def upperRow (a : Nat) := ((List.range 24).drop (a+1)).map (flipCount a)
theorem counts_0 : upperRow 0 = [1826, 1922, 1826, 1826, 1826, 1826, 1826, 1922, 1826, 1826, 1826, 2598, 823, 823, 1091, 1962, 823, 823, 823, 823, 1091, 1962, 1091] := by decide +kernel
theorem counts_1 : upperRow 1 = [1826, 1826, 1826, 1826, 1826, 1922, 1826, 1826, 1826, 1922, 1091, 1962, 823, 1091, 823, 1962, 823, 823, 823, 1091, 823, 2598] := by decide +kernel
theorem counts_2 : upperRow 2 = [1826, 1653, 1653, 1653, 1653, 1735, 1826, 1653, 1653, 1962, 1440, 1440, 823, 599, 602, 1440, 602, 602, 823, 599, 823] := by decide +kernel
theorem counts_3 : upperRow 3 = [1922, 1826, 1922, 1826, 1826, 1826, 1826, 1826, 1091, 823, 1962, 2598, 823, 823, 823, 1962, 823, 1091, 823, 1091] := by decide +kernel
theorem counts_4 : upperRow 4 = [1653, 1735, 1653, 1653, 1826, 1653, 1653, 823, 1440, 599, 1962, 1440, 602, 602, 599, 1440, 823, 602, 823] := by decide +kernel
theorem counts_5 : upperRow 5 = [1653, 1653, 1653, 1922, 1735, 1653, 823, 602, 1440, 823, 1440, 1440, 599, 602, 599, 1962, 602, 823] := by decide +kernel
theorem counts_6 : upperRow 6 = [1653, 1653, 1826, 1653, 1653, 823, 602, 599, 1962, 602, 1440, 1440, 599, 602, 823, 1440, 823] := by decide +kernel
theorem counts_7 : upperRow 7 = [1653, 1826, 1653, 1735, 823, 599, 602, 823, 1440, 599, 1440, 1440, 602, 823, 602, 1962] := by decide +kernel
theorem counts_8 : upperRow 8 = [1826, 1653, 1653, 1962, 602, 602, 823, 599, 1440, 602, 1440, 1440, 823, 599, 823] := by decide +kernel
theorem counts_9 : upperRow 9 = [1922, 1826, 1091, 823, 823, 1091, 823, 823, 1962, 823, 1962, 2598, 823, 1091] := by decide +kernel
theorem counts_10 : upperRow 10 = [1653, 823, 1440, 602, 823, 602, 602, 599, 1440, 599, 1962, 1440, 823] := by decide +kernel
theorem counts_11 : upperRow 11 = [823, 599, 1440, 823, 602, 599, 602, 602, 1440, 823, 1440, 1962] := by decide +kernel
theorem counts_12 : upperRow 12 = [1826, 1826, 1826, 1922, 1826, 1826, 1826, 1826, 1826, 1922, 1826] := by decide +kernel
theorem counts_13 : upperRow 13 = [1653, 1826, 1653, 1735, 1653, 1653, 1653, 1826, 1653, 1922] := by decide +kernel
theorem counts_14 : upperRow 14 = [1922, 1653, 1653, 1653, 1735, 1653, 1826, 1653, 1826] := by decide +kernel
theorem counts_15 : upperRow 15 = [1826, 1826, 1826, 1922, 1826, 1826, 1826, 1826] := by decide +kernel
theorem counts_16 : upperRow 16 = [1653, 1653, 1653, 1653, 1826, 1735, 1826] := by decide +kernel
theorem counts_17 : upperRow 17 = [1653, 1653, 1653, 1826, 1653, 1922] := by decide +kernel
theorem counts_18 : upperRow 18 = [1653, 1735, 1922, 1653, 1826] := by decide +kernel
theorem counts_19 : upperRow 19 = [1653, 1826, 1653, 1826] := by decide +kernel
theorem counts_20 : upperRow 20 = [1922, 1653, 1826] := by decide +kernel
theorem counts_21 : upperRow 21 = [1826, 1826] := by decide +kernel
theorem counts_22 : upperRow 22 = [1826] := by decide +kernel
theorem counts_23 : upperRow 23 = [] := by decide +kernel
def upperTable := (List.range 24).map upperRow
theorem allCounts : upperTable = [[1826, 1922, 1826, 1826, 1826, 1826, 1826, 1922, 1826, 1826, 1826, 2598, 823, 823, 1091, 1962, 823, 823, 823, 823, 1091, 1962, 1091], [1826, 1826, 1826, 1826, 1826, 1922, 1826, 1826, 1826, 1922, 1091, 1962, 823, 1091, 823, 1962, 823, 823, 823, 1091, 823, 2598], [1826, 1653, 1653, 1653, 1653, 1735, 1826, 1653, 1653, 1962, 1440, 1440, 823, 599, 602, 1440, 602, 602, 823, 599, 823], [1922, 1826, 1922, 1826, 1826, 1826, 1826, 1826, 1091, 823, 1962, 2598, 823, 823, 823, 1962, 823, 1091, 823, 1091], [1653, 1735, 1653, 1653, 1826, 1653, 1653, 823, 1440, 599, 1962, 1440, 602, 602, 599, 1440, 823, 602, 823], [1653, 1653, 1653, 1922, 1735, 1653, 823, 602, 1440, 823, 1440, 1440, 599, 602, 599, 1962, 602, 823], [1653, 1653, 1826, 1653, 1653, 823, 602, 599, 1962, 602, 1440, 1440, 599, 602, 823, 1440, 823], [1653, 1826, 1653, 1735, 823, 599, 602, 823, 1440, 599, 1440, 1440, 602, 823, 602, 1962], [1826, 1653, 1653, 1962, 602, 602, 823, 599, 1440, 602, 1440, 1440, 823, 599, 823], [1922, 1826, 1091, 823, 823, 1091, 823, 823, 1962, 823, 1962, 2598, 823, 1091], [1653, 823, 1440, 602, 823, 602, 602, 599, 1440, 599, 1962, 1440, 823], [823, 599, 1440, 823, 602, 599, 602, 602, 1440, 823, 1440, 1962], [1826, 1826, 1826, 1922, 1826, 1826, 1826, 1826, 1826, 1922, 1826], [1653, 1826, 1653, 1735, 1653, 1653, 1653, 1826, 1653, 1922], [1922, 1653, 1653, 1653, 1735, 1653, 1826, 1653, 1826], [1826, 1826, 1826, 1922, 1826, 1826, 1826, 1826], [1653, 1653, 1653, 1653, 1826, 1735, 1826], [1653, 1653, 1653, 1826, 1653, 1922], [1653, 1735, 1922, 1653, 1826], [1653, 1826, 1653, 1826], [1922, 1653, 1826], [1826, 1826], [1826], []] := by
  change [upperRow 0, upperRow 1, upperRow 2, upperRow 3, upperRow 4, upperRow 5, upperRow 6, upperRow 7, upperRow 8, upperRow 9, upperRow 10, upperRow 11, upperRow 12, upperRow 13, upperRow 14, upperRow 15, upperRow 16, upperRow 17, upperRow 18, upperRow 19, upperRow 20, upperRow 21, upperRow 22, upperRow 23] = _
  rw [counts_0, counts_1, counts_2, counts_3, counts_4, counts_5, counts_6, counts_7, counts_8, counts_9, counts_10, counts_11, counts_12, counts_13, counts_14, counts_15, counts_16, counts_17, counts_18, counts_19, counts_20, counts_21, counts_22, counts_23]
theorem minimum_change : upperTable.flatten.min? = some 599 := by rw [allCounts]; decide
theorem nearest_single_flips : upperTable.flatten.count 599 = 16 := by rw [allCounts]; decide
#print axioms counts_0
#print axioms counts_1
#print axioms counts_2
#print axioms counts_3
#print axioms counts_4
#print axioms counts_5
#print axioms counts_6
#print axioms counts_7
#print axioms counts_8
#print axioms counts_9
#print axioms counts_10
#print axioms counts_11
#print axioms counts_12
#print axioms counts_13
#print axioms counts_14
#print axioms counts_15
#print axioms counts_16
#print axioms counts_17
#print axioms counts_18
#print axioms counts_19
#print axioms counts_20
#print axioms counts_21
#print axioms counts_22
#print axioms counts_23
#print axioms allCounts
#print axioms minimum_change
#print axioms nearest_single_flips
end PEqualNP.Research.Punctured24

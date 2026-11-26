import FormulaMass
namespace PEqualNP.Research.TripleCertificate
open Finset TripleFormulaMass
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
def row (i : Fin 20) : Nat := ([35, 69, 137, 273, 518, 1034, 2066, 4108, 8212, 16408, 608, 1184, 2336, 4288, 8512, 16768, 5632, 10752, 19456, 28672] : List Nat).getD i.val 0
def col (i : Fin 25) : Nat := ([510, 3645, 4035, 4060, 12891, 13221, 13242, 15462, 15481, 15751, 15768, 21655, 21865, 21878, 23210, 23221, 23371, 23380, 26316, 26323, 26413, 26418, 26862, 26865, 26895] : List Nat).getD i.val 0
def plus (i : Fin 25) : Nat := ([65520, 466830, 516222, 524286, 747117, 760221, 786429, 817635, 1015791, 1047039, 227820, 895323, 874155, 917499, 702165, 1032159, 1046271, 374490, 446262, 1044351, 1040319, 642873, 983031, 929607, 970935] : List Nat).getD i.val 0
def minus (i : Fin 25) : Nat := ([983040, 581632, 525184, 0, 301056, 262752, 0, 33292, 0, 0, 1043, 152576, 131408, 0, 16650, 0, 0, 2085, 4169, 0, 0, 8326, 0, 65712, 76800] : List Nat).getD i.val 0
def twice (i : Fin 25) : Nat := ([0, 0, 0, 524289, 0, 0, 262146, 0, 32784, 1536, 0, 0, 0, 131076, 0, 16416, 2304, 0, 0, 4224, 8256, 0, 65544, 0, 0] : List Nat).getD i.val 0
def triangle (x : Fin 15 → Bool) := (x 0 && x 1 && x 5) || (x 0 && x 2 && x 6) || (x 0 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 2 && x 9) || (x 1 && x 3 && x 10) || (x 1 && x 4 && x 11) || (x 2 && x 3 && x 12) || (x 2 && x 4 && x 13) || (x 3 && x 4 && x 14) || (x 5 && x 6 && x 9) || (x 5 && x 7 && x 10) || (x 5 && x 8 && x 11) || (x 6 && x 7 && x 12) || (x 6 && x 8 && x 13) || (x 7 && x 8 && x 14) || (x 9 && x 10 && x 12) || (x 9 && x 11 && x 13) || (x 10 && x 11 && x 14) || (x 12 && x 13 && x 14)

def p (r : Fin 20) (i : Fin 15) := (row r).testBit i.val
def q (c : Fin 25) (i : Fin 15) := (col c).testBit i.val
def wt (r : Fin 20) (c : Fin 25) : Int :=
  if (plus c).testBit r.val then 1 else if (minus c).testBit r.val then -1
  else if (twice c).testBit r.val then -2 else 0
def allowed (i : Fin 15) := (univ.filter (fun r => p r i=true)).powerset
def score (i : Fin 15) (s : Finset (Fin 20)) : Int :=
  ∑ c∈univ.filter (fun c => q c i=false),max 0 (∑ r∈s,wt r c)
def bad (i : Fin 15) := (allowed i).filter (fun s => 6 < score i s)
theorem positives : ∀ r, triangle (p r)=true := by decide +kernel
theorem negatives : ∀ c, triangle (q c)=false := by decide +kernel
theorem total : mass wt univ univ=260 := by decide +kernel
theorem cap0 : bad 0=∅ := by decide +kernel
theorem cap1 : bad 1=∅ := by decide +kernel
theorem cap2 : bad 2=∅ := by decide +kernel
theorem cap3 : bad 3=∅ := by decide +kernel
theorem cap4 : bad 4=∅ := by decide +kernel
theorem cap5 : bad 5=∅ := by decide +kernel
theorem cap6 : bad 6=∅ := by decide +kernel
theorem cap7 : bad 7=∅ := by decide +kernel
theorem cap8 : bad 8=∅ := by decide +kernel
theorem cap9 : bad 9=∅ := by decide +kernel
theorem cap10 : bad 10=∅ := by decide +kernel
theorem cap11 : bad 11=∅ := by decide +kernel
theorem cap12 : bad 12=∅ := by decide +kernel
theorem cap13 : bad 13=∅ := by decide +kernel
theorem cap14 : bad 14=∅ := by decide +kernel

theorem cap (i : Fin 15) : bad i=∅ := by
  fin_cases i
  · exact cap0
  · exact cap1
  · exact cap2
  · exact cap3
  · exact cap4
  · exact cap5
  · exact cap6
  · exact cap7
  · exact cap8
  · exact cap9
  · exact cap10
  · exact cap11
  · exact cap12
  · exact cap13
  · exact cap14

theorem test_bound (i : Fin 15) (s : Finset (Fin 20)) (hs : s∈allowed i) :
    score i s ≤ 6 := by
  by_contra! h
  have m : s∈bad i := mem_filter.mpr ⟨hs,h⟩
  simpa [cap] using m
theorem formula_lower (f : Formula (Fin 15)) (exact_on : ∀ x,f.eval x=triangle x) :
    44 ≤ f.leaves := by
  have h := weight_bound p q wt 6 (atom_from_columns p q wt 6 test_bound) f univ univ
    (fun r _ => (exact_on _).trans (positives r)) (fun c _ => (exact_on _).trans (negatives c))
  rw [total] at h
  omega
end PEqualNP.Research.TripleCertificate

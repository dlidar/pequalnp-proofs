import PEqualNP.Research.L_meta_10623_costs

namespace PEqualNP.Research.EncoderBounds
open PEqualNP.CircuitLowerBounds PEqualNP.Research.TriangleChannels PEqualNP.Research.TriangleCosts

def encode (gs : List Gate) (a b : ℕ) (x : Tri) : Pair :=
  ((Circuit.mk gs a).eval (List.ofFn x), (Circuit.mk gs b).eval (List.ofFn x))

theorem init_mem (i : ℕ) : raw.getD i 0 ∈ initial := by
  by_cases small : i < 3
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [raw] using Nat.le_of_not_lt small)]
    decide

theorem at_least_three (gs : List Gate) (ok : legal gs) (a b : ℕ)
    (valid : sufficient (encode gs a b)) : 3 ≤ gs.length := by
  by_contra! h
  obtain ⟨w, good, reads⟩ := coverage noneDecodes gs ok raw initial 2 (by omega)
    (by decide) (by decide) init_mem checked_two
  let u := (run gs raw).getD a 0
  let v := (run gs raw).getD b 0
  have bad : pairOK u v = false := by
    simpa using (List.all_eq_true.mp (List.all_eq_true.mp good u (reads a)) v (reads b))
  have act : pairOK u v = true := by
    apply decide_eq_true
    intro i j eq
    apply valid
    simpa only [u,v,output_table gs ok,encode] using eq
  simp_all

theorem table_ext {u v : T} (h : ∀ r : Fin 8, bit r u = bit r v) : u = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i,hi⟩

theorem low_high_tables : ∀ r : Fin 8,
    bit r 254 = low (read3 r) ∧ bit r 232 = high (read3 r) := by decide +kernel

theorem at_least_five (gs : List Gate) (ok : legal gs) (a b : ℕ)
    (fits : ∀ x, encode gs a b x = (low x,high x)) : 5 ≤ gs.length := by
  by_contra! h
  obtain ⟨w, good, reads⟩ := coverage lacksThermometer gs ok raw initial 4 (by omega)
    (by decide) (by decide) init_mem checked_four
  have ha : (run gs raw).getD a 0 = 254 := table_ext (fun r => by
    rw [output_table _ ok, (low_high_tables r).1]
    exact congrArg Prod.fst (fits (read3 r)))
  have hb : (run gs raw).getD b 0 = 232 := table_ext (fun r => by
    rw [output_table _ ok, (low_high_tables r).2]
    exact congrArg Prod.snd (fits (read3 r)))
  have aa : (254 : T) ∈ w := ha ▸ reads a
  have bb : (232 : T) ∈ w := hb ▸ reads b
  change (!(w.contains 232 && w.contains 254)) = true at good
  rw [List.contains_iff_mem.mpr bb,List.contains_iff_mem.mpr aa] at good
  contradiction

def sortCost (c : Fin 3 → Bool) := if (List.finRange 3).any (fun i => c i != c 0) then 0 else 2

theorem uniform_left : ∀ c : Fin 3 → Bool, sortCost c ≠ 0 → c 0 = true →
    ∀ x, colored c x = (low x,high x) := by decide +kernel
theorem uniform_right : ∀ c : Fin 3 → Bool, sortCost c ≠ 0 → c 0 = false →
    ∀ x, colored c x = (high x,low x) := by decide +kernel
theorem cost_cases : ∀ c : Fin 3 → Bool, sortCost c = 0 ∨ sortCost c = 2 := by decide +kernel

theorem encoder_budget (c : Fin 3 → Bool) (gs : List Gate) (ok : legal gs) (a b : ℕ)
    (fits : ∀ x, encode gs a b x = colored c x) : 3 + sortCost c ≤ gs.length := by
  rcases cost_cases c with h | h
  · simp only [h,Nat.add_zero]
    exact at_least_three gs ok a b (fun x y he => color_valid c x y (by simpa only [← fits] using he))
  · have ne : sortCost c ≠ 0 := by omega
    rw [h]
    cases hc : c 0
    · apply at_least_five gs ok b a
      intro x
      have e := (fits x).trans (uniform_right c ne hc x)
      exact Prod.ext (congrArg Prod.snd e) (congrArg Prod.fst e)
    · exact at_least_five gs ok a b (fun x => (fits x).trans (uniform_left c ne hc x))

def splitGates : List Gate := [⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.or,[2,4]⟩]
def sortedGates : List Gate := [⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.and,[3,2]⟩,⟨.or,[4,5]⟩,⟨.or,[3,2]⟩]

theorem split_sharp : splitGates.length = 3 ∧
    ∀ x, encode splitGates 3 5 x = colored ![true,true,false] x := by decide +kernel
theorem uniform_sharp : sortedGates.length = 5 ∧
    ∀ x, encode sortedGates 7 6 x = (low x,high x) := by decide +kernel

end PEqualNP.Research.EncoderBounds

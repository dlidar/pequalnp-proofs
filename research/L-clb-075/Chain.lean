import PEqualNP.Outside.L_clb_067

namespace RankedCyclicChain
open PEqualNP.Outside.L_clb_067_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket
def disabled : Fin 9 → Nat := ![70423,70422,70420,70416,70400,70144,69632,4096,0]
def answer : Fin 9 → Fin 32 := ![31,30,26,22,15,9,7,5,3]
def row (t : Fin 9) (i : Fin 5) (p : Fin 2 → Bool) : Bool :=
  !(disabled t).testBit (4*i.val + (p 0).toNat + 2*(p 1).toNat)
def inputs (t : Fin 9) : List Bool :=
  (List.ofFn (fun i : Fin 5 => List.ofFn (fun p : Fin 4 => row t i (fun j => p.val.testBit j.val)))).flatten
def sols (t : Fin 9) : Finset (Fin 32) :=
  Finset.univ.filter (fun z => ∀ i : Fin 5,
    row t i (fun j => z.val.testBit (5-1-((i.val+j.val)%5))) = true)
set_option maxRecDepth 8192 in
theorem table_certificate : ∀ t, 3 < (sols t).card ∧ ∀ z ∈ sols t,
    ((sols t).filter (fun y => y.val < z.val)).card = 3 → z = answer t := by decide
theorem length_certificate : ∀ t, (inputs t).length=20 := by decide
theorem increasing : ∀ t : Fin 8, ∀ i : Fin 20,
    (inputs t.castSucc).getD i.val false = true → (inputs t.succ).getD i.val false = true := by decide
theorem falls : ∀ t : Fin 8, ∃ p : Fin 5,
    (answer t.castSucc).val.testBit (4-p.val) = true ∧
    (answer t.succ).val.testBit (4-p.val) = false := by decide

theorem four_inverters (C : Circuit) (outBit : Fin 5 → Fin (20+C.size))
    (fan : FanInTwo C)
    (correct : ∀ t, 3 < (sols t).card → ∃ z ∈ sols t,
      ((sols t).filter (fun y => y.val < z.val)).card=3 ∧
      ∀ p : Fin 5, (C.wires (inputs t)).getD (outBit p).val false = z.val.testBit (4-p.val)) :
    4 ≤ notCount C := by
  have hout (t : Fin 9) (p : Fin 5) :
      (C.wires (inputs t)).getD (outBit p).val false = (answer t).val.testBit (4-p.val) := by
    obtain ⟨z,hz,hr,he⟩ := correct t (table_certificate t).1
    rw [← (table_certificate t).2 z hz hr]
    exact he p
  have mono : ∀ t : Fin 8, ∀ i < 20, (inputs t.castSucc).getD i false = true →
      (inputs t.succ).getD i false = true := fun t i hi => increasing t ⟨i,hi⟩
  have allDrops : drops (I:=20) inputs C.gates = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    obtain ⟨p,ha,hb⟩ := falls t
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (outBit p).val, (outBit p).isLt, (hout _ p).trans ha, (hout _ p).trans hb⟩
  have h := markov_drops_bound inputs length_certificate mono C.gates (fun g hg =>
    ⟨by simpa using (fan g hg).1, (fan g hg).2⟩)
  rw [allDrops, Finset.card_univ, Fintype.card_fin] at h
  change 8+1 ≤ 2^notCount C at h
  by_contra! small
  generalize he : notCount C = u at *
  interval_cases u <;> norm_num at h
theorem full_table_bound (C : Circuit) (outBit : Fin 5 → Fin (20+C.size))
    (fan : FanInTwo C)
    (correct : ∀ table : Fin 5 → (Fin 2 → Bool) → Bool,
      let ins := (List.ofFn (fun i : Fin 5 => List.ofFn (fun p : Fin 4 => table i (fun j => p.val.testBit j.val)))).flatten
      let good := (Finset.univ : Finset (Fin 32)).filter (fun z => ∀ i : Fin 5,
        table i (fun j => z.val.testBit (5-1-((i.val+j.val)%5))) = true)
      3 < good.card → ∃ z ∈ good, (good.filter (fun y => y.val < z.val)).card = 3 ∧
        ∀ p : Fin 5, (C.wires ins).getD (outBit p).val false = z.val.testBit (4-p.val)) :
    4 ≤ notCount C := four_inverters C outBit fan (fun t => correct (row t))

end RankedCyclicChain

#print axioms RankedCyclicChain.four_inverters

#print axioms RankedCyclicChain.table_certificate
#print axioms RankedCyclicChain.length_certificate
#print axioms RankedCyclicChain.increasing
#print axioms RankedCyclicChain.falls
#print axioms RankedCyclicChain.full_table_bound

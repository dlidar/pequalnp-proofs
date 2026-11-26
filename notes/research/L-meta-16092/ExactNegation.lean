import RootProof
namespace PEqualNP.Research.Signed16092
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32000 in
set_option maxHeartbeats 20000000 in
theorem rejection : search 8 rows=false := whole_reject root_checked

theorem binary_lower (gs : List Gate) (o : Nat) (hf : FanInTwo ⟨gs,o⟩)
    (ev : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=F5 x) : 9 ≤ binaryCost gs :=
  bound_from_search rows rfl (by decide) rejection samples gs o (fun g hg => hf g hg) ev

theorem exact_negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069192 * 2 ^ 32 + 3901227008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  rintro ⟨⟨gs,o⟩,hf,⟨g,mem,op,_⟩,sz,ev⟩
  have bound := binary_lower gs o hf ev
  have short : binaryCost gs < gs.length :=
    (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
      ⟨g,mem,by simp [isBinary,op]⟩
  change gs.length≤9 at sz
  omega
#print axioms exact_negation
end PEqualNP.Research.Signed16092

import ExactNegation
import Upper16092
namespace PEqualNP.Research.Signed16092
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem minimum_size (s : Nat) : HasCircuitSize 6 F5 s ↔ 9 ≤ s := by
  constructor
  · rintro ⟨⟨gs,o⟩,hf,sz,ev⟩
    have b := binary_lower gs o hf ev
    have c : binaryCost gs ≤ gs.length := List.length_filter_le _ _
    change gs.length ≤ s at sz;omega
  · intro h
    refine ⟨nine,?_,by rw [nine_size]; exact h,nine_eval⟩
    intro g hg;obtain ⟨op,arity⟩ := nine_monotone g hg
    exact ⟨op.elim Or.inl (fun o => Or.inr (Or.inl o)),arity⟩
def ten : Circuit := ⟨nine.gates ++ [⟨.not,[0]⟩],nine.output⟩
-- The assigned condition allows the additional inverter to be unused.
theorem ten_active_budget (s : Nat) :
    (∃ C : Circuit, FanInTwo C ∧ (∃ g∈C.gates,g.op=.not ∧ g.inputs.length=1) ∧
      C.size ≤ s ∧ ∀ x : Fin 6 → Bool,C.eval (List.ofFn x)=F5 x) ↔ 10 ≤ s := by
  constructor
  · rintro ⟨C,fan,inv,sz,ev⟩;by_contra! low
    exact exact_negation ⟨C,fan,inv,by omega,ev⟩
  · intro h
    refine ⟨ten,?_,⟨⟨.not,[0]⟩,by simp [ten],rfl,rfl⟩,?_,?_⟩
    · intro g hg;rcases List.mem_append.mp hg with old|last
      · obtain ⟨op,arity⟩ := nine_monotone g old
        exact ⟨op.elim Or.inl (fun o => Or.inr (Or.inl o)),arity⟩
      · obtain rfl := List.mem_singleton.mp last
        exact ⟨Or.inr (Or.inr rfl), by decide⟩
    · exact h
    · decide +kernel
#print axioms minimum_size
#print axioms ten_active_budget
end PEqualNP.Research.Signed16092

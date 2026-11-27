import Reference
namespace Graph31116
open PEqualNP.CircuitLowerBounds

def MonoOK (g : List Gate) := ∀ v∈g,(v.op=.and ∨ v.op=.or) ∧ v.inputs.length≤2
def OneOK (g : List Gate) := (∀ v∈g,(v.op=.and ∨ v.op=.or ∨ v.op=.not) ∧ v.inputs.length≤2) ∧
  ∀ i j : Fin g.length,(g.get i).op=.not → (g.get j).op=.not → i=j
def Correct (g : List Gate) (o : Nat) := ∀ x : Fin 8 → Bool, Circuit.eval ⟨g,o⟩ (List.ofFn x)=target x
def Saving := ¬ ∀ g o, OneOK g → Correct g o → ∃ g' o', MonoOK g' ∧ g'.length≤g.length ∧ Correct g' o'

theorem finite_saving : Saving ↔ ∃ g o, OneOK g ∧ Correct g o ∧ g.length≤13 ∧
    ∀ g' o', MonoOK g' → Correct g' o' → g.length<g'.length := by
  classical
  constructor
  · intro no
    by_contra absent
    apply no;intro g o ok exactAt
    by_cases h : 14 ≤ g.length
    · exact ⟨candidate.gates,candidate.output,monotone_gates,h,computes⟩
    · by_contra allTooBig
      apply absent
      refine ⟨g,o,ok,exactAt,by omega,?_⟩
      intro g' o' m c
      by_contra small
      exact allTooBig ⟨g',o',m,by omega,c⟩
  · rintro ⟨g,o,ok,c,_,short⟩ repl
    obtain ⟨g',o',m,le,cc⟩ := repl g o ok c
    exact (Nat.not_lt_of_ge le) (short g' o' m cc)

theorem if_monotone_lower (bound : ∀ g o, MonoOK g → Correct g o → 14≤g.length) :
    Saving ↔ ∃ g o, OneOK g ∧ Correct g o ∧ g.length≤13 := by
  rw [finite_saving]
  constructor
  · rintro ⟨g,o,ok,c,le,_⟩;exact ⟨g,o,ok,c,le⟩
  · rintro ⟨g,o,ok,c,le⟩;refine ⟨g,o,ok,c,le,?_⟩
    intro g' o' m c';have v:=bound _ _ m c';omega
end Graph31116

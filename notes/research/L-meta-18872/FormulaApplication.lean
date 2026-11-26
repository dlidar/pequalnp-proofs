import IndependentTriple18872
import TriangleCertificate
import SingleInverter

namespace PEqualNP.Research.TripleApplication
open TripleFormulaMass TripleCertificate IndependentTriple18872 SingleInverter
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dual {I} : Formula I → Formula I
  | .var i => .var i
  | .conj f g => .disj (dual f) (dual g)
  | .disj f g => .conj (dual f) (dual g)
theorem dual_leaves {I} (f : Formula I) : (dual f).leaves=f.leaves := by
  induction f <;> simp_all [dual,Formula.leaves]
theorem dual_eval {I} (f : Formula I) (x : I → Bool) :
    (dual f).eval x = !(f.eval (fun i => !(x i))) := by
  induction f <;> simp_all [dual,Formula.eval]
theorem target_triangle (x : Fin 15 → Bool) : target (fun i => !(x i))=triangle x := by
  simp [target,triangle]
theorem reference_uses {n} {x : Fin n → Bool} (pre post : List Gate) (args : List Nat) (o : Nat)
    (a : MonoGates pre) (b : MonoGates post)
    (lo : (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.replicate n false)=true)
    (hi : (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.replicate n true)=false) :
    (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.ofFn x)=inverse pre args x := by
  rw [split_eval]
  exact context_identity (controlled pre post o) (inverse pre args)
    (controlled_mono pre post a b o)
    (by rw [← split_eval]; simpa using lo) (by rw [← split_eval]; simpa using hi) _ _

/-- A monotone context surrounding a single negated monotone formula may share
    both the raw inputs and the negated value arbitrarily. -/
theorem inverted_formula_lower (f : Formula (Fin 15)) (h : Signal 15 → Bool → Bool)
    (mono : ∀ x y a b, Extends x y → (a=true → b=true) → h x a=true → h y b=true)
    (computes : ∀ x,h x (!(f.eval x))=target x) : 44 ≤ f.leaves := by
  have eq := context_identity h (fun x => !(f.eval x)) mono
    ((computes _).trans (by decide)) ((computes _).trans (by decide))
  have lower := formula_lower (dual f) (by
    intro x
    rw [dual_eval,← target_triangle,← computes,eq])
  simpa [dual_leaves] using lower

theorem prefix_formula_lower (pre post : List Gate) (args : List Nat) (o : Nat)
    (a : MonoGates pre) (b : MonoGates post) (f : Formula (Fin 15))
    (operand : ∀ x,inverse pre args x = !(f.eval x))
    (computes : ∀ x : Signal 15,
      (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.ofFn x)=target x) : 44 ≤ f.leaves := by
  apply inverted_formula_lower f (controlled pre post o) (controlled_mono pre post a b o)
  intro x
  rw [← operand,← split_eval,computes]

theorem target_normalized {s} (pre post : List Gate) (args : List Nat) (o : Nat)
    (a : MonoGates pre) (b : MonoGates post)
    (fan : FanInTwo (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o))
    (budget : (pre ++ ⟨.not,args⟩ :: post).length ≤ s)
    (computes : ∀ x : Signal 15,
      (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.ofFn x)=target x) :
    ∃ C : Circuit,C.gates=pre ++ [⟨.not,args⟩] ∧ C.output=15+pre.length ∧
      FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Signal 15,C.eval (List.ofFn x)=target x := by
  refine ⟨⟨_,_⟩,rfl,rfl,?_,?_,?_⟩
  · intro g hg
    apply fan
    change g ∈ pre ++ [⟨.not,args⟩] at hg
    simpa using (show g ∈ (pre ++ [⟨.not,args⟩]) ++ post from List.mem_append_left _ hg)
  · simp [Circuit.size] at budget ⊢
    omega
  · intro x
    rw [← remove_suffix pre post args o a b _ _ x,computes]
    · simpa using (computes (fun _ => false)).trans (show target (fun _ => false)=true by decide)
    · simpa using (computes (fun _ => true)).trans (show target (fun _ => true)=false by decide)
end PEqualNP.Research.TripleApplication

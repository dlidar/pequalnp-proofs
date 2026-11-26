import CachedBase
import PEqualNP.Defs
namespace PEqualNP.Research.Cached9815
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds TripleFormulaMass Finset
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def formula : Formula EdgeInput := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var 0) (.disj (.var 8) (.var 10))) (.conj (.var 1) (.disj (.disj (.var 7) (.var 9)) (.var 13)))) (.conj (.var 2) (.disj (.var 8) (.var 13)))) (.conj (.var 3) (.disj (.disj (.var 7) (.var 11)) (.var 12)))) (.conj (.var 4) (.disj (.disj (.var 10) (.var 11)) (.var 13)))) (.conj (.var 5) (.disj (.disj (.var 9) (.var 10)) (.var 12)))) (.conj (.var 6) (.disj (.disj (.var 8) (.var 9)) (.var 11))))
theorem formula_size : formula.leaves=26 := rfl
def upperCircuit : Circuit := ⟨[⟨.or, [8, 10]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [1, 17]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [2, 19]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [12, 21]⟩, ⟨.and, [3, 22]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 24]⟩, ⟨.and, [4, 25]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 27]⟩, ⟨.and, [5, 28]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 30]⟩, ⟨.and, [6, 31]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [20, 33]⟩, ⟨.or, [23, 34]⟩, ⟨.or, [26, 35]⟩, ⟨.or, [29, 36]⟩, ⟨.or, [32, 37]⟩],38⟩
theorem upper_size : upperCircuit.size=25 := rfl
theorem upper_fan : FanInTwo upperCircuit := by
  intro g hg
  simp [upperCircuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem circuit_formula (x : EdgeInput → Bool) : upperCircuit.eval (List.ofFn x)=formula.eval x := by
  have hx : List.ofFn x=[x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13] := rfl
  rw [hx]
  simp only [upperCircuit,formula,Formula.eval,Circuit.eval,Circuit.wires,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ,GateOp.eval,List.any_cons,List.all_cons,List.any_nil,List.all_nil,id_eq,Bool.and_true,Bool.or_false]
  ac_rfl
theorem formula_correct (x : EdgeInput → Bool) : formula.eval x=target x := by
  simp only [target,formula,Formula.eval]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  decide +kernel
theorem upper_bound : HasCircuitSize 14 target 25 := ⟨upperCircuit,upper_fan,upper_size.le,fun x => (circuit_formula x).trans (formula_correct x)⟩
private def weights : Array (Array Int) := #[#[0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, -6, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 6, 0, 6, 0, 0, 0, 3, 0, 0, 0, -6, 0, 0, 0, 3, 0, 0], #[0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, -3, -3, 0, 0, 6, 0, 0, 0, -3, 0, 0], #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, -6, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 3, 0, 0], #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 6, 0, 0], #[0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, -6, 0, 0], #[0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0], #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 3, 0, 0, -3, 0, 0, 6, 0, 0, -3, 0, 0, -3, 0], #[0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, -6, 0, 0, 3, 0, 0, 3, 0], #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, -3, 0, -3, -3, 0, 0, 3, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, -3, 0, 6, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 3, -3, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, -3, 0, 0], #[0, 0, 6, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, -3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], #[0, 0, 0, 6, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0], #[0, 0, 0, 0, 0, 6, 0, 0, 0, -6, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, -6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], #[0, 0, 0, 0, 0, -6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6, 0, 0]]
private def wt : Weights := fun r c => (weights[r.val]!)[c.val]!
theorem ordinary_bound (f : Formula EdgeInput) (correct : ∀ x,f.eval x=target x) : 26 ≤ f.leaves := by
  have raws : rawOK wt 12=true := by decide +kernel
  have tot : mass wt univ univ = 312 := by decide +kernel
  have atom := atom_from_columns pos neg wt 12 (by
    intro i s hs
    have h := List.all_eq_true.mp raws i (by simp)
    exact score_ok _ _ _ _ (by simpa using h) _ hs)
  have e := weight_bound pos neg wt 12 atom f univ univ (fun r _ => (correct _).trans (rows_ok r))
    (fun c _ => (correct _).trans (cols_ok c))
  rw [tot] at e
  omega
theorem ordinary_optimum (s : Nat) : (∃ f : Formula EdgeInput, f.leaves ≤ s ∧ ∀ x,f.eval x=target x) ↔ 26 ≤ s := by
  constructor
  · rintro ⟨f,le,c⟩
    exact (ordinary_bound f c).trans le
  · intro h
    exact ⟨formula, by rwa [formula_size],formula_correct⟩
def useful : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.var none)) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem useful_size : useful.leaves=25 := rfl
theorem useful_eval (x : EdgeInput → Bool) : useful.eval (fill false 8 10 x)=target x := by
  rw [← formula_correct];rfl
end PEqualNP.Research.Cached9815

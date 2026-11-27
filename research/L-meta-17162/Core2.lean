import FormulaMass

namespace FourRowCore.Core2
open Finset PEqualNP.Research.TripleFormulaMass

abbrev Input := Fin 10
abbrev Row := Fin 12
abbrev Col := Fin 12
def edges : List (Input × Input) := [(0, 4), (1, 4), (0, 5), (2, 5), (1, 6), (2, 6), (0, 7), (3, 7), (1, 8), (3, 8), (2, 9), (3, 9)]
def target (x : Input → Bool) := edges.any fun e => x e.1 && x e.2
def pos (r : Row) (i : Input) := ((#[17, 18, 33, 36, 66, 68, 129, 136, 258, 264, 516, 520] : Array Nat)[r.val]!).testBit i.val
def neg (c : Col) (i : Input) := ((#[15, 28, 42, 73, 120, 134, 261, 404, 515, 674, 833, 1008] : Array Nat)[c.val]!).testBit i.val
private def weights : Array (Array Int) := #[#[0, 0, 0, 3, 4, 0, 3, 4, 0, -6, 6, 2], #[0, 0, 3, 0, 4, 3, 0, 4, 0, 6, -6, 2], #[0, 0, 0, 3, 4, 0, 0, -6, 3, 4, 6, 2], #[0, 3, 0, 0, 4, 3, 0, 6, 0, 4, -6, 2], #[0, 0, 3, 0, 4, 0, 0, -6, 3, 6, 4, 2], #[0, 3, 0, 0, 4, 0, 3, 6, 0, -6, 4, 2], #[0, 0, 0, 0, -6, 0, 3, 4, 3, 4, 6, 2], #[0, 3, 3, 0, 6, 0, 0, 4, 0, 4, -6, 2], #[0, 0, 0, 0, -6, 3, 0, 4, 3, 6, 4, 2], #[0, 3, 0, 3, 6, 0, 0, 4, 0, -6, 4, 2], #[0, 0, 0, 0, -6, 3, 3, 6, 0, 4, 4, 2], #[0, 0, 3, 3, 6, 0, 0, -6, 0, 4, 4, 2]]
def wt (r : Row) (c : Col) := (weights[r.val]!)[c.val]!
def witness : Formula Input := (.disj (.disj (.disj (.conj (.var 0) (.disj (.disj (.var 4) (.var 5)) (.var 7))) (.conj (.var 1) (.disj (.disj (.var 4) (.var 6)) (.var 8)))) (.conj (.var 2) (.disj (.disj (.var 5) (.var 6)) (.var 9)))) (.conj (.var 3) (.disj (.disj (.var 7) (.var 8)) (.var 9))))
theorem witness_size : witness.leaves = 16 := by decide +kernel
theorem witness_ok (x : Input → Bool) : witness.eval x = target x := by
  simp [witness,Formula.eval,target,edges,Bool.and_or_distrib_left,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]

theorem rows_ok : ∀ r,target (pos r)=true := by decide +kernel
theorem cols_ok : ∀ c,target (neg c)=false := by decide +kernel
def passes (i : Input) : Bool :=
  decide (((univ.filter (fun r => pos r i=true)).powerset.filter fun s =>
    12 < ∑ c∈univ.filter (fun c => neg c i=false),max 0 (∑ r∈s,wt r c)).card = 0)
theorem certificate : ∀ i,passes i=true := by decide +kernel
theorem total_mass : mass wt univ univ = 192 := by decide +kernel

theorem formula_lower (f : Formula Input) (correct : ∀ x,f.eval x=target x) :
    16 ≤ f.leaves := by
  have bound := atom_from_columns pos neg wt 12 (by
    intro i s hs
    by_contra! bad
    have emp := Finset.card_eq_zero.mp (of_decide_eq_true (certificate i))
    have mem : s ∈ (univ.filter (fun r => pos r i=true)).powerset.filter (fun t =>
        12 < ∑ c∈univ.filter (fun c => neg c i=false),max 0 (∑ r∈t,wt r c)) := mem_filter.mpr ⟨hs,bad⟩
    rw [emp] at mem
    exact notMem_empty _ mem)
  have h := weight_bound pos neg wt 12 bound f univ univ
    (fun r _ => (correct _).trans (rows_ok r)) (fun c _ => (correct _).trans (cols_ok c))
  rw [total_mass] at h
  omega
end FourRowCore.Core2

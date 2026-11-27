import FormulaMass

namespace FourRowCore.Core0
open Finset PEqualNP.Research.TripleFormulaMass

abbrev Input := Fin 8
abbrev Row := Fin 8
abbrev Col := Fin 10
def edges : List (Input × Input) := [(0, 4), (1, 4), (0, 5), (2, 5), (1, 6), (3, 6), (2, 7), (3, 7)]
def target (x : Input → Bool) := edges.any fun e => x e.1 && x e.2
def pos (r : Row) (i : Input) := ((#[17, 18, 33, 36, 66, 72, 132, 136] : Array Nat)[r.val]!).testBit i.val
def neg (c : Col) (i : Input) := ((#[15, 28, 42, 56, 69, 84, 131, 162, 193, 240] : Array Nat)[c.val]!).testBit i.val
private def weights : Array (Array Int) := #[#[0, 2, -1, 0, 2, 0, 0, 0, 0, 0], #[0, 2, 2, 0, -1, 0, 0, 0, 0, 0], #[0, -1, 2, 0, 0, 0, 2, 0, 0, 0], #[0, 2, 2, 0, 0, 0, -1, 0, 0, 0], #[0, -1, 0, 0, 2, 0, 2, 0, 0, 0], #[0, 2, 0, 0, 2, 0, -1, 0, 0, 0], #[0, 0, -1, 0, 2, 0, 2, 0, 0, 0], #[0, 0, 2, 0, -1, 0, 2, 0, 0, 0]]
def wt (r : Row) (c : Col) := (weights[r.val]!)[c.val]!
def witness : Formula Input := (.disj (.disj (.disj (.conj (.var 0) (.disj (.var 4) (.var 5))) (.conj (.var 1) (.disj (.var 4) (.var 6)))) (.conj (.var 2) (.disj (.var 5) (.var 7)))) (.conj (.var 3) (.disj (.var 6) (.var 7))))
theorem witness_size : witness.leaves = 12 := by decide +kernel
theorem witness_ok (x : Input → Bool) : witness.eval x = target x := by
  simp [witness,Formula.eval,target,edges,Bool.and_or_distrib_left,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]

theorem rows_ok : ∀ r,target (pos r)=true := by decide +kernel
theorem cols_ok : ∀ c,target (neg c)=false := by decide +kernel
def passes (i : Input) : Bool :=
  decide (((univ.filter (fun r => pos r i=true)).powerset.filter fun s =>
    2 < ∑ c∈univ.filter (fun c => neg c i=false),max 0 (∑ r∈s,wt r c)).card = 0)
theorem certificate : ∀ i,passes i=true := by decide +kernel
theorem total_mass : mass wt univ univ = 24 := by decide +kernel

theorem formula_lower (f : Formula Input) (correct : ∀ x,f.eval x=target x) :
    12 ≤ f.leaves := by
  have bound := atom_from_columns pos neg wt 2 (by
    intro i s hs
    by_contra! bad
    have emp := Finset.card_eq_zero.mp (of_decide_eq_true (certificate i))
    have mem : s ∈ (univ.filter (fun r => pos r i=true)).powerset.filter (fun t =>
        2 < ∑ c∈univ.filter (fun c => neg c i=false),max 0 (∑ r∈t,wt r c)) := mem_filter.mpr ⟨hs,bad⟩
    rw [emp] at mem
    exact notMem_empty _ mem)
  have h := weight_bound pos neg wt 2 bound f univ univ
    (fun r _ => (correct _).trans (rows_ok r)) (fun c _ => (correct _).trans (cols_ok c))
  rw [total_mass] at h
  omega
end FourRowCore.Core0

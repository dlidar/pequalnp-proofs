import Mathlib
import PEqualNP.Defs.Represents

namespace Mask245567Formulas

abbrev Input := Fin 9 → Bool
def row (x : Fin 20) : Input := fun i => decide (i.val = x.val / 5 ∨ i.val = 4 + x.val % 5)
def target (x : Fin 20) : Bool := (245567 : Nat).testBit x.val

theorem separating_rows (i : Fin 9) : ∃ p n : Fin 20,
    target p = true ∧ target n = false ∧ ∀ j : Fin 9, j ≠ i → row p j ≤ row n j := by
  revert i
  decide +kernel

-- An increasing extension to all nine input bits depends on every one of them.
theorem depends_on_each (f : Input → Bool) (h : Monotone f)
    (hf : ∀ p, f (row p) = target p) (i : Fin 9) :
    ∃ x y : Input, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y := by
  obtain ⟨p, n, hp, hn, hle⟩ := separating_rows i
  let x : Input := fun j => if j = i then false else row p j
  have small : x ≤ row n := by
    intro j
    by_cases he : j = i
    · simp [x, he]
    · simpa [x, he] using hle j he
  refine ⟨x, row p, fun j hj => by simp [x, hj], ?_⟩
  have hx := h small
  rw [hf n, hn] at hx
  rw [hf p, hp]
  intro eq
  rw [eq] at hx
  exact (by decide : ¬ (true ≤ false)) hx

inductive Formula where
  | raw (i : Fin 9)
  | conj (a b : Formula)
  | disj (a b : Formula)

def Formula.eval : Formula → Input → Bool
  | .raw i, x => x i
  | .conj a b, x => a.eval x && b.eval x
  | .disj a b, x => a.eval x || b.eval x

def Formula.leaves : Formula → List (Fin 9)
  | .raw i => [i]
  | .conj a b | .disj a b => a.leaves ++ b.leaves

def Formula.gates : Formula → Nat
  | .raw _ => 0
  | .conj a b | .disj a b => a.gates + b.gates + 1

def f0 : Formula := (.disj (.disj (.conj (.disj (.raw 1) (.raw 2)) (.raw 7)) (.disj (.raw 0) (.raw 4))) (.conj (.disj (.disj (.raw 1) (.raw 5)) (.raw 6)) (.disj (.disj (.raw 2) (.raw 8)) (.raw 3))))
theorem check0 : f0.gates = 10 ∧ (∀ x, f0.eval (row x) = target x) ∧ (∀ i : Fin 9, f0.leaves.count i = if i = 1 ∨ i = 2 then 2 else 1) := by decide +kernel
def f1 : Formula := (.disj (.disj (.conj (.raw 2) (.raw 7)) (.disj (.raw 0) (.raw 4))) (.conj (.disj (.disj (.raw 1) (.raw 5)) (.raw 6)) (.disj (.disj (.disj (.raw 2) (.raw 7)) (.raw 8)) (.raw 3))))
theorem check1 : f1.gates = 10 ∧ (∀ x, f1.eval (row x) = target x) ∧ (∀ i : Fin 9, f1.leaves.count i = if i = 2 ∨ i = 7 then 2 else 1) := by decide +kernel
end Mask245567Formulas
#print axioms Mask245567Formulas.separating_rows
#print axioms Mask245567Formulas.depends_on_each
#print axioms Mask245567Formulas.check0
#print axioms Mask245567Formulas.check1

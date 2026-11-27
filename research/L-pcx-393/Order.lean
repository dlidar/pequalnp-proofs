import Mathlib

namespace PinIndex
open Finset
def tag (o : Option Bool) : ℕ := if o.isSome then 1+(o.getD false).toNat else 0
theorem tag_lt (o : Option Bool) : tag o < 3 := by cases o with
  | none => decide
  | some b => cases b <;> decide
theorem tag_injective : Function.Injective tag := by decide
def digits {n : ℕ} (x : Fin n → ℕ) := ∑ i, x i * 3^i.val
theorem digits_cons {n : ℕ} (x : Fin (n+1) → ℕ) :
    digits x = x 0 + 3*digits (fun i => x i.succ) := by
  simp [digits, Fin.sum_univ_succ, pow_succ, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
theorem digits_inj (n : ℕ) (x y : Fin n → ℕ) (hx : ∀ i, x i < 3)
    (hy : ∀ i, y i < 3) (eq : digits x = digits y) : x = y := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [digits_cons,digits_cons] at eq
    have h0 := hx 0
    have h1 := hy 0
    have head : x 0 = y 0 := by omega
    have tail := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => hx _) (fun i => hy _) (by omega)
    funext i
    exact Fin.cases head (fun j => congrFun tail j) i
theorem digits_lt (n : ℕ) (x : Fin n → ℕ) (hx : ∀ i, x i < 3) : digits x < 3^n := by
  induction n with
  | zero => simp [digits]
  | succ n ih =>
    rw [digits_cons,pow_succ]
    have := ih (fun i => x i.succ) (fun i => hx _)
    have := hx 0
    omega
def key {n : ℕ} (p : Bool × Fin n → Option Bool) :=
  ∑ v, tag (p v) * 3^(v.2.val + (if v.1 then n else 0))
theorem key_split {n : ℕ} (p : Bool × Fin n → Option Bool) :
    key p = digits (fun i => tag (p (false,i))) + 3^n * digits (fun i => tag (p (true,i))) := by
  simp [key,digits,Fintype.sum_prod_type,Fintype.sum_bool,pow_add,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc,add_comm]
theorem key_injective (n : ℕ) : Function.Injective (key (n:=n)) := by
  intro p q eq
  rw [key_split,key_split] at eq
  let a := fun (f : Bool × Fin n → Option Bool) b => digits (fun i => tag (f (b,i)))
  have small f b : a f b < 3^n := digits_lt _ _ (fun _ => tag_lt _)
  change a p false + 3^n * a p true = a q false + 3^n * a q true at eq
  have first : a p false = a q false := by
    have h := congrArg (fun x => x % 3^n) eq
    simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (small _ _)] using h
  have second : a p true = a q true := by
    rw [first] at eq
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_left_cancel eq)
  funext ⟨b,i⟩
  apply tag_injective
  apply congrFun (digits_inj n (fun j => tag (p (b,j))) (fun j => tag (q (b,j)))
    (fun _ => tag_lt _) (fun _ => tag_lt _) ?_) i
  cases b <;> assumption
theorem fiber_order {α : Type*} (f : α → ℕ) (hf : Function.Injective f) (s : Finset α) :
    ∃ e : Fin s.card ≃ {a // a ∈ s}, ∀ i j, i < j → f (e i) < f (e j) := by
  classical
  letI : LinearOrder α := LinearOrder.lift' f hf
  exact ⟨(s.orderIsoOfFin rfl).toEquiv,fun i j h => (s.orderIsoOfFin rfl).strictMono h⟩
theorem pin_order {n : ℕ} (s : Finset (Bool × Fin n → Option Bool)) :
    ∃ e : Fin s.card ≃ {p // p ∈ s}, ∀ i j, i < j → key (e i).val < key (e j).val :=
  fiber_order key (key_injective n) s
end PinIndex

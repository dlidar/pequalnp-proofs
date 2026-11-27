import Mathlib

namespace PinPaths
open Finset
variable {S : Type*} {D : Type*} [Fintype D]
def run (next : ℕ → S → D → S) (allow : ℕ → D → Bool) (accept : S → Bool)
    (i : ℕ) (s : S) : (k : ℕ) → (Fin k → D) → Bool
  | 0, _ => accept s
  | k+1, word => allow i (word 0) && run next allow accept (i+1) (next i s (word 0)) k (fun j => word j.succ)
def count (next : ℕ → S → D → S) (allow : ℕ → D → Bool) (accept : S → Bool)
    (i : ℕ) (s : S) : ℕ → ℕ
  | 0 => (accept s).toNat
  | k+1 => ∑ d, if allow i d then count next allow accept (i+1) (next i s d) k else 0
def splitWord (k : ℕ) : (Fin (k+1) → D) ≃ D × (Fin k → D) where
  toFun w := (w 0,fun i => w i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by funext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv p := by cases p; rfl
theorem count_correct (next : ℕ → S → D → S) (allow : ℕ → D → Bool) (accept : S → Bool)
    (i : ℕ) (s : S) (k : ℕ) :
    count next allow accept i s k =
      (univ.filter (fun w : Fin k → D => run next allow accept i s k w)).card := by
  classical
  rw [Finset.card_filter]
  induction k generalizing i s with
  | zero => cases h : accept s <;> simp [run,count,h]
  | succ k ih =>
    rw [← (splitWord (D:=D) k).symm.sum_comp, Fintype.sum_prod_type]
    unfold count
    apply Finset.sum_congr rfl
    intro d _
    cases h : allow i d <;> simp [splitWord,run,h,ih]
theorem count_bound (next : ℕ → S → D → S) (allow : ℕ → D → Bool) (accept : S → Bool)
    (i : ℕ) (s : S) (k : ℕ) :
    count next allow accept i s k ≤ Fintype.card D ^ k := by
  rw [count_correct]
  simpa using Finset.card_le_card (Finset.filter_subset (fun w : Fin k → D => run next allow accept i s k w = true) univ)
theorem no_overflow (next : ℕ → S → Fin 3 → S) (allow : ℕ → Fin 3 → Bool) (accept : S → Bool)
    (i : ℕ) (s : S) {k n : ℕ} (hk : k ≤ 2*n) (hn : 0<n) :
    count next allow accept i s k < 2^(4*n) := by
  have b := count_bound next allow accept i s k
  simp only [Fintype.card_fin] at b
  have strong : 3^(2*n) < 4^(2*n) := Nat.pow_lt_pow_left (by decide) (by omega)
  have eq : 4^(2*n) = 2^(4*n) := by
    rw [show (4:ℕ)=2^2 by decide,← pow_mul]; congr 1 <;> omega
  exact ((b.trans (Nat.pow_le_pow_right (by decide) hk)).trans_lt strong).trans_eq eq
end PinPaths

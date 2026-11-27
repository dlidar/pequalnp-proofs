import Mathlib

namespace TernaryGrid
open Finset

def val (x : Fin 3) : ℤ := if x = 0 then 0 else if x = 1 then -1 else 1
def nz (x : ℤ) : ℕ := if x = 0 then 0 else 1
theorem affine_support (a b : ℤ) :
    2 * nz a ≤ ∑ x : Fin 3, nz (a * val x + b) := by
  rw [Fin.sum_univ_three]
  change 2 * nz a ≤ nz (a*0+b) + nz (a*(-1)+b) + nz (a*1+b)
  simp only [mul_zero,zero_add,mul_neg,mul_one]
  unfold nz
  split_ifs <;> omega

theorem square_support (c a b e : ℤ) :
    4 * nz c ≤ ∑ x : Fin 3, ∑ y : Fin 3,
      nz (c * val x * val y + a * val x + b * val y + e) := by
  have h := affine_support c b
  have hh (x : Fin 3) : 2 * nz (c*val x+b) ≤ ∑ y : Fin 3,
      nz (c * val x * val y + a * val x + b * val y + e) := by
    convert affine_support (c*val x+b) (a*val x+e) using 1
    congr 1
    funext y
    congr 1
    ring
  calc
    4 * nz c = 2 * (2 * nz c) := by omega
    _ ≤ 2 * ∑ x : Fin 3, nz (c*val x+b) := Nat.mul_le_mul_left 2 h
    _ = ∑ x : Fin 3, 2 * nz (c*val x+b) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hh x)

theorem square_sharp :
    (∑ x : Fin 3, ∑ y : Fin 3, nz (val x * val y)) = 4 := by decide

structure Bilinear where
  mixed : ℤ
  left : ℤ
  right : ℤ
  constant : ℤ
deriving DecidableEq

def Bilinear.eval (f : Bilinear) (x y : ℤ) : ℤ :=
  f.mixed*x*y + f.left*x + f.right*y + f.constant
def Bilinear.add (f g : Bilinear) : Bilinear :=
  ⟨f.mixed+g.mixed,f.left+g.left,f.right+g.right,f.constant+g.constant⟩
def Bilinear.sub (f g : Bilinear) : Bilinear :=
  ⟨f.mixed-g.mixed,f.left-g.left,f.right-g.right,f.constant-g.constant⟩
theorem eval_add (f g : Bilinear) (x y : ℤ) :
    (f.add g).eval x y = f.eval x y + g.eval x y := by simp [Bilinear.eval,Bilinear.add]; ring
theorem eval_sub (f g : Bilinear) (x y : ℤ) :
    (f.sub g).eval x y = f.eval x y - g.eval x y := by simp [Bilinear.eval,Bilinear.sub]; ring
theorem distance (f g : Bilinear) (h : f.mixed ≠ g.mixed) :
    4 ≤ ∑ x : Fin 3, ∑ y : Fin 3, if f.eval (val x) (val y) ≠ g.eval (val x) (val y) then 1 else 0 := by
  have hs := square_support (f.sub g).mixed (f.sub g).left (f.sub g).right (f.sub g).constant
  change _ ≤ ∑ x : Fin 3, ∑ y : Fin 3, nz ((f.sub g).eval (val x) (val y)) at hs
  simp_rw [eval_sub] at hs
  simpa [Bilinear.sub, nz, sub_eq_zero, h] using hs
end TernaryGrid

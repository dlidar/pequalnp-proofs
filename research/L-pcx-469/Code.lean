import Decode
import Grid
namespace SpinMass
open Finset TernaryGrid
variable {t k : ℕ}
def vary (e : Pair t) (p : Mask t) (x y : Fin 3) (i : Fin t) : Fin 3 :=
  if i = e.val.1 then x else if i = e.val.2 then y else p i

def interp (f : ℤ → ℤ → ℤ) : Bilinear :=
  ⟨f 1 1 - f 1 0 - f 0 1 + f 0 0, f 1 0 - f 0 0, f 0 1 - f 0 0, f 0 0⟩

def formalEdge (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : ℤ) : ℤ :=
  let z := fun i => if i = e.val.1 then x else if i = e.val.2 then y else sign (p i)
  g.elim 0 (fun u => z u.val.1 * z u.val.2)

theorem interp_edge (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : ℤ) :
    (interp (formalEdge e p g)).eval x y = formalEdge e p g x y ∧
    (interp (formalEdge e p g)).mixed = (if g = some e then 1 else 0) := by
  cases g with
  | none => simp [interp, formalEdge, Bilinear.eval]
  | some u =>
    have hu := u.property
    have he := e.property
    have eqs : u = e ↔ u.val.1 = e.val.1 ∧ u.val.2 = e.val.2 := by
      exact Subtype.ext_iff.trans Prod.ext_iff
    simp only [formalEdge,Option.elim,interp,Bilinear.eval,Option.some.injEq,eqs]
    by_cases h₁ : u.val.1 = e.val.1 <;> by_cases h₂ : u.val.1 = e.val.2 <;>
      by_cases h₃ : u.val.2 = e.val.1 <;> by_cases h₄ : u.val.2 = e.val.2 <;>
      first | (exfalso; omega) | (simp only [if_pos,if_neg,h₁,h₂,h₃,h₄, ne_of_lt he, Ne.symm (ne_of_lt he), ite_self, true_and, false_and, and_true, and_false, ite_true, ite_false]; constructor <;> ring)

theorem formal_semantics (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : Fin 3) :
    formalEdge e p g (val x) (val y) = edgeSign g (vary e p x y) := by
  have h (i : Fin t) : (if i = e.val.1 then val x else if i = e.val.2 then val y else sign (p i)) =
      sign (vary e p x y i) := by
    unfold vary
    split_ifs <;> rfl
  cases g with
  | none => rfl
  | some u => exact congrArg₂ (· * ·) (h u.val.1) (h u.val.2)

def polyModel (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) : Bilinear :=
  let f := fun l => interp (formalEdge e p (G l))
  ⟨∑ l, (f l).mixed, ∑ l, (f l).left, ∑ l, (f l).right, ∑ l, (f l).constant⟩
def mult (G : Fin k → Option (Pair t)) (e : Pair t) : ℕ := (univ.filter (fun l => G l = some e)).card
theorem poly_mixed (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) :
    (polyModel e p G).mixed = (mult G e : ℤ) := by
  change (∑ l, (interp (formalEdge e p (G l))).mixed) = _
  simp_rw [(interp_edge e p _ 0 0).2]
  exact sum_boole _ _
theorem poly_eval (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) (x y : Fin 3) :
    (polyModel e p G).eval (val x) (val y) =
    ((reading G (vary e p x y)).factorization 5 : ℤ) - ((reading G (vary e p x y)).factorization 3 : ℤ) := by
  rw [← signed_reading]
  simp only [polyModel, Bilinear.eval, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  exact ((interp_edge e p (G l) (val x) (val y)).1).trans (formal_semantics e p (G l) x y)

theorem four_masks (G H : Fin k → Option (Pair t)) (e : Pair t) (p : Mask t)
    (h : mult G e ≠ mult H e) :
    4 ≤ ∑ x : Fin 3, ∑ y : Fin 3, if reading G (vary e p x y) ≠ reading H (vary e p x y) then 1 else 0 := by
  have hd := TernaryGrid.distance (polyModel e p G) (polyModel e p H) (by simpa [poly_mixed] using h)
  apply le_trans hd
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  simp_rw [poly_eval]
  by_cases hh : reading G (vary e p x y) = reading H (vary e p x y)
  · simp [hh]
  · simp [hh]; split <;> decide

end SpinMass

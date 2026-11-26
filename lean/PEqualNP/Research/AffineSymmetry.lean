import PEqualNP.Research.AffineMatrix

namespace PEqualNP.Research.AffineSymmetry
open Finset PEqualNP.Research.AffineRectangleCover
set_option maxRecDepth 80000
set_option maxHeartbeats 8000000
def rowMap (g : Fin 4) (i : P) : P :=
  ((#[#[1, 2, 3, 4, 0, 6, 7, 8, 9, 5, 11, 12, 13, 14, 10, 16, 17, 18, 19, 15, 21, 22, 23, 24, 20],
    #[0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24],
    #[0, 1, 2, 3, 4, 6, 7, 8, 9, 5, 12, 13, 14, 10, 11, 18, 19, 15, 16, 17, 24, 20, 21, 22, 23],
    #[0, 2, 4, 1, 3, 5, 7, 9, 6, 8, 10, 12, 14, 11, 13, 15, 17, 19, 16, 18, 20, 22, 24, 21, 23]] : Array (Array P))[g.val]!)[i.val]!
def colMap (g : Fin 4) (i : L) : L :=
  ((#[#[1, 2, 3, 4, 0, 6, 7, 8, 9, 5, 11, 12, 13, 14, 10, 16, 17, 18, 19, 15, 21, 22, 23, 24, 20, 25, 26, 27, 28, 29],
    #[25, 26, 27, 28, 29, 5, 9, 8, 7, 6, 15, 17, 19, 16, 18, 10, 13, 11, 14, 12, 20, 21, 22, 23, 24, 0, 1, 2, 3, 4],
    #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 1, 2, 3, 4, 25, 26, 27, 28, 29],
    #[0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 25, 26, 27, 28, 29]] : Array (Array L))[g.val]!)[i.val]!

theorem row_inj : ∀ (g : Fin 4) (i j : P), rowMap g i = rowMap g j → i=j := by decide +kernel
theorem col_inj : ∀ (g : Fin 4) (i j : L), colMap g i = colMap g j → i=j := by decide +kernel
theorem preserves : ∀ (g : Fin 4) (i : P) (j : L), zero (rowMap g i) (colMap g j) = zero i j := by decide +kernel

def move {α : Type} (f : Fin 4 → α → α) : List (Fin 4) → α → α
  | [], x => x
  | g::t,x => move f t (f g x)

theorem move_inj {α : Type} (f : Fin 4 → α → α) (h : ∀ g, Function.Injective (f g)) (gs : List (Fin 4)) :
    Function.Injective (move f gs) := by
  induction gs with
  | nil => exact fun _ _ he => he
  | cons g t ih => exact ih.comp (h g)

theorem move_zero (gs : List (Fin 4)) (p : P) (l : L) :
    zero (move rowMap gs p) (move colMap gs l) = zero p l := by
  induction gs generalizing p l with
  | nil => rfl
  | cons g t ih => exact (ih _ _).trans (preserves g p l)
end PEqualNP.Research.AffineSymmetry

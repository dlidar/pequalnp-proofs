import CoreLower
import CloneCosts
import Permute
open PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Mask114591Family Mask114591Permute Mask114591CloneLift Mask114591CloneCosts
namespace Mask114591Structural

def core (u : Fin 4) (v : Fin 3) := (759 : Nat).testBit (3*u.val+v.val)
def four (u : Fin 4) (v : Fin 4) := core u (projectLast 0 v)
def five (u : Fin 4) (v : Fin 5) := four u (projectLast 1 v)

def columnOrder : Fin 5 ≃ Fin 5 where
  toFun := ![0,3,1,4,2]
  invFun := ![0,2,4,1,3]
  left_inv := by decide
  right_inv := by decide

theorem original_to_core (s : Nat) : RepSizeAtMost base (s+2) → RepSizeAtMost core s := by
  intro h
  have perm := budget_perm (A := base) (B := five) columnOrder (by decide) h
  have h1 := (duplicate_budget four 1 (s+1) (by decide)).mp perm
  exact (duplicate_budget core 0 s (by decide)).mp h1

theorem exact_negation : ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  intro h
  exact core_no_seven (original_to_core 7 h)

end Mask114591Structural
#print axioms Mask114591Structural.exact_negation

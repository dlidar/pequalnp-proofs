import Mathlib
namespace InverterBridge.Three
/-- Truth tables of the constants, the three input coordinates and their six
two-leaf conjunctions and disjunctions, indexed by the three-bit assignment. -/
def pool : Fin 11 → Nat := ![0,255,170,204,240,170 &&& 204,170 &&& 240,204 &&& 240,170 ||| 204,170 ||| 240,204 ||| 240]
def parallel (x y : Fin 8) : Bool := decide ((x.val &&& y.val) ≠ x.val ∧ (x.val &&& y.val) ≠ y.val)
def allowed (z : Fin 256) (x : Fin 8) : Bool := decide (∀ y : Fin 8, z.val.testBit y.val=true → parallel x y=true)
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
theorem every_zero_set : ∀ z : Fin 256, ∃ i : Fin 11, ∀ x : Fin 8,
  (z.val.testBit x.val=true → (pool i).testBit x.val=false) ∧
  (allowed z x=true → (pool i).testBit x.val=true) := by decide +kernel

theorem two_leaves_required : ∀ i : Fin 5, ¬ (∀ x : Fin 8,
  ((x.val=1) → (pool ⟨i.val,by omega⟩).testBit x.val=false) ∧
  ((x.val=2 ∨ x.val=4 ∨ x.val=6) → (pool ⟨i.val,by omega⟩).testBit x.val=true)) := by decide +kernel
end InverterBridge.Three

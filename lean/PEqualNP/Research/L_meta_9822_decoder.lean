import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PEqualNP.Research.DecoderSlices
/-- Bit order is 00, 10, 01, 11. Each local encoder sees just its own bit. -/
abbrev Table := Fin 16
abbrev Encoder := Fin 4
def pattern (d : Table) (a b : Encoder) : Nat :=
  ((List.range 4).map fun k => if d.val.testBit ((if a.val.testBit (k%2) then 1 else 0) +
    (if b.val.testBit (k/2) then 2 else 0)) then 2^k else 0).sum
def err (s t : Nat) : Nat := ((List.range 4).filter fun i => s.testBit i != t.testBit i).length
def canMeet (d : Table) := ∃ a b : Encoder, pattern d a b = 8
instance (d : Table) : Decidable (canMeet d) := inferInstanceAs (Decidable (∃ _ _, _))
def Mono (s : Table) := s = 0 ∨ s = 8 ∨ s = 10 ∨ s = 12 ∨ s = 14 ∨ s = 15
instance (s : Table) : Decidable (Mono s) := inferInstanceAs (Decidable (_ ∨ _))

/-- No choice of input encoders lets the same decoder realize both AND and OR. -/
theorem incompatible : ∀ d : Table, canMeet d → ∀ a b, pattern d a b ≠ 14 := by decide +kernel

theorem local_lower : ∀ (d s : Table) (a b : Encoder),
    (if canMeet d then (if s=14 then 1 else 0) else (if s=8 then 1 else 0)) ≤
      err s.val (pattern d a b) := by decide +kernel

theorem local_and : ∀ s : Table, Mono s → ∃ a b : Encoder,
    err s.val (pattern 8 a b) = (if s=14 then 1 else 0) := by decide +kernel
theorem local_or : ∀ s : Table, Mono s → ∃ a b : Encoder,
    err s.val (pattern 14 a b) = (if s=8 then 1 else 0) := by decide +kernel

def count (keys : List Nat) (f : Nat → Table) (s : Table) :=
  ((keys.map fun i => if f i=s then 1 else 0) : List Nat).sum
def loss (keys : List Nat) (f : Nat → Table) (d : Table) (a b : Nat → Encoder) :=
  (keys.map fun i => err (f i).val (pattern d (a i) (b i))).sum

theorem fixed_lower (keys : List Nat) (f : Nat → Table) (d : Table) (a b : Nat → Encoder) :
    (if canMeet d then count keys f 14 else count keys f 8) ≤ loss keys f d a b := by
  induction keys with
  | nil => simp [count,loss]
  | cons k ks ih =>
    have h := local_lower d (f k) (a k) (b k)
    by_cases hm : canMeet d <;> simp only [hm,↓reduceIte,count,loss,List.map_cons,List.sum_cons] at * <;> omega

theorem optimal_fixed (keys : List Nat) (f : Nat → Table) (hm : ∀ k, Mono (f k)) :
    (∃ a b, loss keys f 8 a b = count keys f 14) ∧
    (∃ a b, loss keys f 14 a b = count keys f 8) := by
  have join (d t : Table) (h : ∀ k, ∃ a b, err (f k).val (pattern d a b) = (if f k=t then 1 else 0)) :
      ∃ a b, loss keys f d a b = count keys f t := by
    choose a b h using h
    exact ⟨a,b,by simp [loss,count,h]⟩
  exact ⟨join 8 14 (fun k => local_and _ (hm k)),join 14 8 (fun k => local_or _ (hm k))⟩

/-- Minimum Hamming error, allowing any fixed binary decoder, including nonmonotone gates,
and arbitrary encoder pairs chosen separately for every setting of the shared variables. -/
theorem optimum (keys : List Nat) (f : Nat → Table) (hm : ∀ k, Mono (f k)) :
    (∀ d a b, min (count keys f 8) (count keys f 14) ≤ loss keys f d a b) ∧
    ∃ d a b, loss keys f d a b = min (count keys f 8) (count keys f 14) := by
  constructor
  · intro d a b
    have h := fixed_lower keys f d a b
    split at h <;> omega
  · obtain ⟨ha,hb⟩ := optimal_fixed keys f hm
    by_cases le : count keys f 8 ≤ count keys f 14
    · obtain ⟨a,b,h⟩ := hb
      exact ⟨14,a,b,by rwa [min_eq_left le]⟩
    · obtain ⟨a,b,h⟩ := ha
      exact ⟨8,a,b,by rwa [min_eq_right (by omega)]⟩
end PEqualNP.Research.DecoderSlices

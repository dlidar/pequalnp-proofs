import Mathlib
namespace PEqualNP.Research.CachedFlagTerms
abbrev Mask := BitVec 27
def on (t x : Mask) : Prop := t &&& x = t
instance (t x : Mask) : Decidable (on t x) := inferInstanceAs (Decidable (_ = _))
theorem inherited (t a b z : Mask) (ha : on t a) (hb : on t b) (hz : on (a &&& b) z) : on t z := by
  unfold on at *
  have ht : t &&& (a &&& b) = t := by rw [← BitVec.and_assoc,ha,hb]
  calc
    t &&& z = (t &&& (a &&& b)) &&& z := congrArg (· &&& z) ht.symm
    _ = t := by rw [BitVec.and_assoc,hz,ht]
/-- Distinct selected positive rows need different conjunction terms. -/
theorem packing {k m : ℕ} (r : Fin k → Mask) (ns : List Mask) (ts : Fin m → Mask)
    (sep : ∀ i j, i < j → ∃ z ∈ ns, on (r i &&& r j) z)
    (pos : ∀ i, ∃ j, on (ts j) (r i)) (neg : ∀ j z, z ∈ ns → ¬on (ts j) z) : k ≤ m := by
  classical
  choose f hf using pos
  have ordered : ∀ i j, i < j → f i ≠ f j := by
    intro i j lt eq
    obtain ⟨z,hz,inside⟩ := sep i j lt
    exact neg (f i) z hz (inherited _ _ _ _ (hf i) (eq.symm ▸ hf j) inside)
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i j with h|h|h
    · exact (ordered i j h eq).elim
    · exact h
    · exact (ordered j i h eq.symm).elim
  simpa using Fintype.card_le_of_injective f inj

end PEqualNP.Research.CachedFlagTerms

#print axioms PEqualNP.Research.CachedFlagTerms.on
#print axioms PEqualNP.Research.CachedFlagTerms.inherited
#print axioms PEqualNP.Research.CachedFlagTerms.packing

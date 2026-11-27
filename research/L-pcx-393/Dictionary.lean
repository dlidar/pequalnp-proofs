import Mathlib
import PEqualNP.Outside.L_pcx_375

namespace PinDictionary
open Finset PEqualNP.Outside.L_pcx_375_aux
abbrev Pin (n : ℕ) := Bool × Fin n → Option Bool
abbrev Hist (n : ℕ) := Fin (n+1) → Fin (n+1) → ℕ
def hist {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :=
  ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,i))).card = r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,σ i))).card = b.val)).card
def pair {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : Bool) : Equiv.Perm (Fin n) :=
  if h then σ else Equiv.refl _
theorem hist_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :
    hist σ p r b = histDef (fun h i => pair σ h i) p (r,b) := by
  simp [hist, histDef, Bool.forall_bool, pair]
def scale {n : ℕ} (z : ℕ × ((Fin (n+1) × Fin (n+1)) → ℕ)) : Hist n :=
  fun r b => 2^z.1 * z.2 (r,b)
theorem common_dictionary : ∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
    let n := t+1
    ∃ D : Finset (Hist n), D.card ≤ (n+1)*2^(C*(1+Nat.sqrt n)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Pin n), hist σ p ∈ D := by
  classical
  obtain ⟨C,hC,base⟩ := PEqualNP.Outside.L_pcx_375
  refine ⟨C,hC,fun t => ?_⟩
  let n := t+1
  haveI : NeZero n := ⟨Nat.succ_ne_zero t⟩
  let H := (Finset.univ : Finset (Pin n)).image (histDef (ringDef n))
  have bound : H.card ≤ 2^(C*(1+Nat.sqrt n)) := (base t).2.1
  refine ⟨((Finset.range (n+1)) ×ˢ H).image scale,?_,?_⟩
  · apply card_image_le.trans
    rw [Finset.card_product, Finset.card_range]
    exact Nat.mul_le_mul_left (n+1) bound
  · intro σ p
    obtain ⟨p',f,hf,rep⟩ := ((base t).2.2 (pair σ)).2 p
    refine mem_image.mpr ⟨(f,histDef (ringDef n) p'),mem_product.mpr ⟨mem_range.mpr (by omega),mem_image.mpr ⟨p',mem_univ _,rfl⟩⟩,?_⟩
    funext r b
    rw [hist_eq]
    exact (rep (r,b)).symm

def fiber {n : ℕ} (σ : Equiv.Perm (Fin n)) (allow : Bool × Fin n → Option Bool → Bool) (H : Hist n) :=
  (univ : Finset (Pin n)).filter (fun p => hist σ p = H ∧ ∀ v, allow v (p v) = true)
theorem outside_empty {n : ℕ} (D : Finset (Hist n))
    (covers : ∀ σ (p : Pin n), hist σ p ∈ D)
    (σ : Equiv.Perm (Fin n)) (allow : Bool × Fin n → Option Bool → Bool) (H : Hist n) (ho : H ∉ D) :
    fiber σ allow H = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨eq,_⟩ := (mem_filter.mp hp).2
  exact ho (eq ▸ covers σ p)
end PinDictionary

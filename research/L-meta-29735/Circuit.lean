import Rank
import PEqualNP.Outside.L_meta_25647

noncomputable section
namespace FieldCoverage
open Module LinearMap
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.Outside.L_meta_25647_aux
abbrev F := ZMod 2

def fits {n m : ℕ} (G : Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin 1 → ℕ), ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
    ∀ j, (depthsOf (n+m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents G ⟨C.gates,tap j⟩

theorem fits_iff {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    fits G t ↔ (anchor u v (fun i j => b2z (G i j))).rank ≤ 2*t := by
  rw [PEqualNP.Outside.L_meta_25647_aux.main]
  constructor
  · rintro ⟨C,tap,hr,hg,hc,h⟩
    exact ⟨⟨C.gates,tap 0⟩,⟨hg,hr,(h 0).2⟩,(h 0).1,hc⟩
  · rintro ⟨C,⟨hg,hr,he⟩,hd,hc⟩
    exact ⟨C,fun _ => C.output,hr,hg,hc,fun _ => ⟨hd,he⟩⟩

variable {E K : Type} [Field E] [Field K] [Algebra F E] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] [FiniteDimensional E K]
variable {k : ℕ}

def label (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (D : K →ₗ[E] K) :=
  fun (i j : Fin (k+1)) => decide (bit (D (points b i) * points b j) ≠ 0)

theorem b2z_test (x : ZMod 2) [Decidable (x ≠ 0)] : b2z (decide (x ≠ 0)) = x := by
  by_cases h : x = 0
  · subst x; simp [b2z]
  · have hx : x = 1 := by fin_cases x <;> first | rfl | exact False.elim (h rfl)
    simp [h,hx,b2z]

theorem anchor_label (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (D : K →ₗ[E] K) :
    anchor 0 0 (fun i j => b2z (label b bit D i j)) = matrixOf b bit (D.restrictScalars F) := by
  ext i j
  simp only [anchor,label,b2z_test,matrixOf,LinearMap.restrictScalars_apply]
  simp [points]

theorem fits_label (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (D : K →ₗ[E] K) (t : ℕ) : fits (label b bit D) t ↔
    finrank F E * finrank E (range D) ≤ 2*t := by
  rw [fits_iff _ 0 0,anchor_label,extension_rank b bit hb]

theorem label_add (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (A B : K →ₗ[E] K) :
    label b bit (A+B) = fun x y => xor (label b bit A x y) (label b bit B x y) := by
  funext i j
  apply b2z_inj
  rw [b2z_xor]
  simp only [label,b2z_test,LinearMap.add_apply,add_mul,map_add]

theorem rank_cutoff {h m t r : ℕ} (hh : 0 < h) (hl : h*m-h ≤ 2*t)
    (hu : 2*t < h*m) : h*r ≤ 2*t ↔ r < m := by
  constructor
  · intro hr
    by_contra! hmr
    have := Nat.mul_le_mul_left h hmr
    omega
  · intro hr
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_lt hr
    subst m
    have hm := Nat.mul_le_mul_left h (Nat.le_add_right r d)
    rw [Nat.mul_succ] at hl
    omega

theorem fits_singular (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (D : K →ₗ[E] K) (t : ℕ) (hh : 0 < finrank F E)
    (hl : finrank F E * finrank E K - finrank F E ≤ 2*t)
    (hu : 2*t < finrank F E * finrank E K) :
    fits (label b bit D) t ↔ ¬ Function.Injective D := by
  rw [fits_label b bit hb,rank_cutoff hh hl hu]
  constructor
  · intro h inj
    rw [finrank_range_of_inj inj] at h
    omega
  · intro h
    apply Submodule.finrank_lt
    intro top
    exact h (LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp top))

theorem rank_one_cost (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (D : K →ₗ[E] K) (hr : finrank E (range D) = 1) (t : ℕ) :
    fits (label b bit D) t ↔ (finrank F E+1)/2 ≤ t := by
  rw [fits_label b bit hb,hr,Nat.mul_one]
  omega

end FieldCoverage

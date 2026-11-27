import Circuit

namespace FieldCoverage
open Module LinearMap Submodule
noncomputable section
variable {E K : Type} [Field E] [Field K] [Algebra E K]

def oneTable (f : K →ₗ[E] E) : K →ₗ[E] K := f.smulRight 1

theorem oneTable_apply (f : K →ₗ[E] E) (x : K) : oneTable f x = algebraMap E K (f x) := by
  simp [oneTable, Algebra.smul_def]

theorem oneTable_rank (f : K →ₗ[E] E) (hf : Function.Surjective f) :
    finrank E (range (oneTable f)) = 1 := by
  have eqr : range (oneTable f) = E ∙ (1 : K) := by
    ext x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨v,rfl⟩; exact ⟨f v,rfl⟩
    · rintro ⟨c,rfl⟩
      obtain ⟨v,rfl⟩ := hf c
      exact ⟨v,rfl⟩
  rw [eqr,finrank_span_singleton one_ne_zero]

theorem singular_iff_slope (z : K) (C : K →ₗ[E] K) :
    ¬ Function.Injective (LinearMap.mul E K z - C) ↔
      ∃ x : K, x ≠ 0 ∧ C x = z*x := by
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro h; by_contra! hn; apply h; apply eq_bot_iff.mpr; intro x hx
    by_contra hne
    apply hn x hne
    exact (sub_eq_zero.mp (show z*x-C x = 0 from hx)).symm
  · rintro ⟨x,hx,he⟩ h
    have hmem : x ∈ ker (LinearMap.mul E K z - C) := sub_eq_zero.mpr he.symm
    rw [h] at hmem
    exact hx hmem

theorem singular_oneTable (z : K) (hz : z ≠ 0) (f : K →ₗ[E] E) :
    ¬ Function.Injective (LinearMap.mul E K z - oneTable f) ↔ f z⁻¹ = 1 := by
  rw [singular_iff_slope]
  constructor
  · rintro ⟨x,hx,he⟩
    have hn : f x ≠ 0 := by
      intro h
      simpa [oneTable_apply,h,hz,hx] using he
    have scaled : (f x) • z⁻¹ = x := by
      rw [Algebra.smul_def,← oneTable_apply,he]
      field_simp
    have eq := congrArg f scaled
    rw [map_smul,smul_eq_mul] at eq
    exact mul_left_cancel₀ hn (by simpa using eq : f x * f z⁻¹ = f x * 1)
  · intro h
    exact ⟨z⁻¹,inv_ne_zero hz,by simp [oneTable_apply,h,hz]⟩

theorem covers_reciprocal_hyperplane
    [Algebra F E] [Algebra F K] [IsScalarTower F E K] [FiniteDimensional E K]
    {k : ℕ} (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (z : K) (hz : z ≠ 0) (f : K →ₗ[E] E) (t : ℕ) (hh : 0 < finrank F E)
    (hl : finrank F E * finrank E K - finrank F E ≤ 2*t)
    (hu : 2*t < finrank F E * finrank E K) :
    fits (fun x y => xor (label b bit (LinearMap.mul E K z) x y)
      (label b bit (oneTable f) x y)) t ↔ f z⁻¹ = 1 := by
  rw [← label_add,fits_singular b bit hb _ t hh hl hu]
  have hchar : CharP K 2 := charP_of_injective_algebraMap
    (algebraMap F K).injective 2
  have neg : -(oneTable f) = oneTable f := by ext x; exact CharTwo.neg_eq _
  rw [← singular_oneTable z hz f,sub_eq_add_neg,neg]

end
end FieldCoverage

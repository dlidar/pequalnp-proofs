import Mathlib

noncomputable section
namespace FieldCoverage
open Module LinearMap Submodule

variable {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E]
  [Algebra F K] [Algebra E K] [IsScalarTower F E K]
variable {k : ℕ}

def points (b : Basis (Fin k) F K) : Fin (k+1) → K := Fin.cases 0 b

theorem span_points (b : Basis (Fin k) F K) :
    span F (Set.range (points b)) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i.succ,rfl⟩

def readings (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) : K →ₗ[F] (Fin (k+1) → F) where
  toFun x j := bit (x * points b j)
  map_add' x y := by ext j; simp [add_mul]
  map_smul' c x := by ext j; simp [smul_mul_assoc]

theorem readings_injective (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0) :
    Function.Injective (readings b bit) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : readings b bit x = 0 := hx
  by_contra hn
  have hx0 : x ≠ 0 := hn
  let f : K →ₗ[F] F := bit.comp (LinearMap.mul F K x)
  have hf : f = 0 := by
    apply b.ext
    intro i
    exact congrFun hz i.succ
  apply hb
  ext y
  have he := LinearMap.congr_fun hf (x⁻¹*y)
  simpa [f,← mul_assoc,hx0] using he

def matrixOf (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (D : K →ₗ[F] K) :
    Matrix (Fin (k+1)) (Fin (k+1)) F := fun i j => bit (D (points b i) * points b j)

theorem matrix_rank (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (D : K →ₗ[F] K) : (matrixOf b bit D).rank = finrank F (range D) := by
  classical
  let f := readings b bit
  have hset : Set.range (matrixOf b bit D).row = (f.comp D) '' Set.range (points b) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [Matrix.rank_eq_finrank_span_row,hset,← Submodule.map_span,span_points,Submodule.map_top,LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective f (readings_injective b bit hb) _).finrank_eq.symm

theorem extension_rank [FiniteDimensional E K] (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (hb : bit ≠ 0) (D : K →ₗ[E] K) :
    (matrixOf b bit (D.restrictScalars F)).rank =
    finrank F E * finrank E (range D) := by
  rw [matrix_rank b bit hb, LinearMap.range_restrictScalars]
  exact (Module.finrank_mul_finrank F E (range D)).symm

end FieldCoverage

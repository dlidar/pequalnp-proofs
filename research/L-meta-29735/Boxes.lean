import Hyperplanes

namespace FieldCoverage
open Module LinearMap
open scoped BigOperators
noncomputable section
variable {E K : Type} [Field E] [Field K] [Algebra E K]
variable {m : ℕ}

def levelFunctional (b : Basis (Fin m) E K) (i : Fin m) (a : E) : K →ₗ[E] E :=
  a⁻¹ • b.coord i

theorem level_surjective (b : Basis (Fin m) E K) (i : Fin m) (a : E) (ha : a ≠ 0) :
    Function.Surjective (levelFunctional b i a) := by
  intro y
  refine ⟨(a*y) • b i, ?_⟩
  simp [levelFunctional, Basis.coord_apply]
  field_simp

theorem level_eq (b : Basis (Fin m) E K) (i : Fin m) (a : E) (ha : a ≠ 0) (w : K) :
    levelFunctional b i a w = 1 ↔ b.coord i w = a := by
  change a⁻¹ * b.coord i w = 1 ↔ _
  rw [inv_mul_eq_iff_eq_mul₀ ha,mul_one]

def frozenBox [Fintype E] [DecidableEq E] (b : Basis (Fin m) E K)
    (L : Fin m → Finset E) : Finset K :=
  (Fintype.piFinset (fun i => (L i)ᶜ)).map
    (b.equivFun.symm.toEquiv.trans (Equiv.inv K)).toEmbedding

theorem box_member [Fintype E] [DecidableEq E] (b : Basis (Fin m) E K)
    (L : Fin m → Finset E) (z : K) :
    z ∈ frozenBox b L ↔ ∀ i, b.coord i z⁻¹ ∉ L i := by
  classical
  rw [frozenBox,Finset.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩ i
    have hi := (Fintype.mem_piFinset.mp hw) i
    change b.coord i (b.equivFun.symm w)⁻¹⁻¹ ∉ L i
    rw [inv_inv]
    change b.equivFun (b.equivFun.symm w) i ∉ L i
    rw [LinearEquiv.apply_symm_apply]
    exact Finset.mem_compl.mp hi
  · intro h
    refine ⟨b.equivFun z⁻¹,Fintype.mem_piFinset.mpr (fun i => Finset.mem_compl.mpr (h i)),?_⟩
    change (b.equivFun.symm (b.equivFun z⁻¹))⁻¹ = z
    simp

theorem box_count [Fintype E] [DecidableEq E] (b : Basis (Fin m) E K)
    (L : Fin m → Finset E) :
    (frozenBox b L).card = ∏ i, (Fintype.card E - (L i).card) := by
  simp [frozenBox,Finset.card_compl]

theorem box_family
    [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
    [Algebra F E] [Algebra F K] [IsScalarTower F E K] [FiniteDimensional E K]
    {k : ℕ} (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hb : bit ≠ 0)
    (b : Basis (Fin m) E K) (L : Fin m → Finset E) (hlvl : ∀ i, 0 ∉ L i)
    (t : ℕ) (hh : 0 < finrank F E)
    (hl : finrank F E * finrank E K - finrank F E ≤ 2*t)
    (hu : 2*t < finrank F E * finrank E K) :
    ∃ (C : ((i : Fin m) × (L i)) → K →ₗ[E] K) (S : Finset K),
      (0 : K) ∉ S ∧
      (∀ u, finrank E (range (C u)) = 1 ∧ fits (label basis bit (C u)) ((finrank F E+1)/2)) ∧
      (∀ z ∈ S, ∃ u, fits (fun x y => xor (label basis bit (LinearMap.mul E K z) x y)
        (label basis bit (C u) x y)) t) ∧
      S.card + ∏ i, (Fintype.card E - (L i).card) = Fintype.card K := by
  classical
  let C := fun u : (i : Fin m) × (L i) => oneTable (levelFunctional b u.1 u.2.val)
  have nz (u : (i : Fin m) × (L i)) : u.2.val ≠ 0 := fun eq => hlvl u.1 (eq ▸ u.2.property)
  have zeroBox : 0 ∈ frozenBox b L := (box_member b L 0).mpr (by simpa using hlvl)
  refine ⟨C,(frozenBox b L)ᶜ,by simpa using zeroBox,?_,?_,?_⟩
  · intro u
    have rank : finrank E (range (C u)) = 1 :=
      oneTable_rank _ (level_surjective b u.1 _ (nz u))
    exact ⟨rank,(rank_one_cost basis bit hb _ rank _).mpr le_rfl⟩
  · intro z hz
    have hn := Finset.mem_compl.mp hz
    have hne : z ≠ 0 := fun h => hn (h ▸ zeroBox)
    rw [box_member] at hn
    push_neg at hn
    obtain ⟨i,hi⟩ := hn
    let u : (i : Fin m) × (L i) := ⟨i,_,hi⟩
    refine ⟨u,(covers_reciprocal_hyperplane basis bit hb z hne _ t hh hl hu).mpr ?_⟩
    exact (level_eq b _ _ (nz u) _).mpr rfl
  · rw [← box_count b L,Finset.card_compl_add_card]

end
end FieldCoverage

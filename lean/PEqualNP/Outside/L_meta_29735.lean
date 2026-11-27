import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25647

namespace PEqualNP.Outside.L_meta_29735_aux

section Rank
open Module LinearMap Submodule

variable {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E]
  [Algebra F K] [Algebra E K] [IsScalarTower F E K]
variable {k : ℕ}

noncomputable def points (b : Basis (Fin k) F K) : Fin (k+1) → K := Fin.cases 0 b

theorem span_points (b : Basis (Fin k) F K) :
    span F (Set.range (points b)) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i.succ,rfl⟩

noncomputable def readings (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) : K →ₗ[F] (Fin (k+1) → F) where
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

noncomputable def matrixOf (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (D : K →ₗ[F] K) :
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
end Rank

section Circuit
open Module LinearMap
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.Outside.L_meta_25647_aux
abbrev F := ZMod 2

noncomputable def fits {n m : ℕ} (G : Fin n → Fin m → Bool) (t : ℕ) : Prop :=
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

noncomputable def label (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (D : K →ₗ[E] K) :=
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
end Circuit

section Hyperplanes
open Module LinearMap Submodule

variable {E K : Type} [Field E] [Field K] [Algebra E K]

noncomputable def oneTable (f : K →ₗ[E] E) : K →ₗ[E] K := f.smulRight 1

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
end Hyperplanes

section Boxes
open Module LinearMap
open scoped BigOperators

variable {E K : Type} [Field E] [Field K] [Algebra E K]
variable {m : ℕ}

noncomputable def levelFunctional (b : Basis (Fin m) E K) (i : Fin m) (a : E) : K →ₗ[E] E :=
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

noncomputable def frozenBox [Fintype E] [DecidableEq E] (b : Basis (Fin m) E K)
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
end Boxes

section Budget
open Module LinearMap

noncomputable def levelSize (q a b i : ℕ) := if i<a then q-1 else if i=a then b else 0

theorem level_totals (q b : ℕ) (hq : 1 < q) (hb : b < q) (m a : ℕ)
    (ha : a ≤ m) (hend : a=m → b=0) :
    (∑ i : Fin m, levelSize q a b i) = a*(q-1)+b ∧
    (∏ i : Fin m, (q-levelSize q a b i)) =
      q^(m-a)-b*q^(m-a-1) := by
  induction m generalizing a with
  | zero =>
    have : a=0 := by omega
    subst a
    simp [hend rfl]
  | succ m ih =>
    cases a with
    | zero =>
      rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
      have rest (i : Fin m) : levelSize q 0 b i.succ.val = 0 := by simp [levelSize]
      simp only [rest,Nat.sub_zero,Finset.sum_const_zero,add_zero,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin,Nat.zero_mul,zero_add,Nat.add_one_sub_one]
      simp [levelSize,Nat.sub_mul,pow_succ']
    | succ a =>
      have r := ih a (by omega) (by intro e; exact hend (by omega))
      have step (i : Fin m) : levelSize q (a+1) b i.succ.val = levelSize q a b i.val := by
        simp [levelSize]
      have head : levelSize q (a+1) b 0 = q-1 := by simp [levelSize]
      rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
      simp only [Fin.val_zero,head,step,r.1,r.2,Nat.succ_sub_succ_eq_sub]
      have one : q-(q-1)=1 := by omega
      rw [one,one_mul,Nat.succ_mul]
      omega

theorem allocate {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (m c : ℕ) (hc : c ≤ m*(Fintype.card E-1)) :
    let q := Fintype.card E
    let a := c/(q-1)
    let b := c%(q-1)
    ∃ L : Fin m → Finset E, (∀ i, 0 ∉ L i) ∧
      (∑ i, (L i).card) = c ∧
      (∏ i, (q-(L i).card)) = q^(m-a)-b*q^(m-a-1) := by
  classical
  intro q a b
  have hq : 1 < q := Fintype.one_lt_card
  have hp : 0 < q-1 := by omega
  have hsplit : (q-1)*a+b=c := Nat.div_add_mod c (q-1)
  have hb : b < q-1 := Nat.mod_lt c hp
  have ha : a ≤ m := by
    by_contra! hx
    have hm := Nat.mul_lt_mul_of_pos_left hx hp
    change c ≤ m*(q-1) at hc
    rw [Nat.mul_comm m] at hc
    omega
  have hend : a=m → b=0 := by
    rintro rfl
    change c ≤ a*(q-1) at hc
    rw [Nat.mul_comm a] at hc
    omega
  let D : Finset E := Finset.univ.erase 0
  have cd : D.card=q-1 := by simp [D,q]
  have e (i : Fin m) : ∃ T ⊆ D, T.card = levelSize q a b i := by
    apply Finset.exists_subset_card_eq
    rw [cd]
    unfold levelSize
    split_ifs <;> omega
  choose L sub card using e
  have totals := level_totals q b hq (by omega) m a ha hend
  refine ⟨L,?_,?_,?_⟩
  · intro i hi
    have := sub i hi
    simpa [D] using this
  · simp only [card,totals.1]
    rwa [Nat.mul_comm]
  · simpa only [card] using totals.2
end Budget

section Attain
theorem exact_attainment :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (h m t budget : ℕ), 0 < h → 0 < m →
  let F := ZMod 2
  let E := GaloisField 2 h
  let q := 2^h
  let k := h*m
  let n := k+1
  k-h ≤ 2*t → 2*t < k →
  ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    [FiniteDimensional E K], Module.finrank E K = m →
    ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      let point : Fin n → K := Fin.cases 0 basis
      let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
      let table := fun (C : K →ₗ[E] K) (x y : Fin n) => decide (bit (C (point x) * point y) ≠ 0)
      let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) =>
        ∀ z ∈ S, ∃ i : Fin l,
          fits n n 1 (fun _ x y => xor (mult z x y) (table (C i) x y)) t
      let rk := fun (D : K →ₗ[E] K) => Module.finrank E (LinearMap.range D)
      let c := min budget (m*(q-1))
      let a := c/(q-1)
      let b := c % (q-1)
      let left := q^(m-a) - b*q^(m-a-1)
      (∃ (C : Fin c → (K →ₗ[E] K)) (S : Finset K),
        (0 : K) ∉ S ∧
        (∀ i : Fin c, rk (C i) = 1 ∧ fits n n 1 (fun _ => table (C i)) ((h+1)/2)) ∧
        serves c C S ∧ S.card + left = q^m) := by
  classical
  intro nonlinear depths fits h m t budget hh hm F E q k n hl hu K _ _ _ _ _ hdim basis bit hb point mult table serves rk c a b left
  letI : Fintype E := Fintype.ofFinite E
  letI : Finite K := Module.finite_of_finite E
  letI : Fintype K := Fintype.ofFinite K
  have hed : Module.finrank PEqualNP.Outside.L_meta_29735_aux.F E = h := GaloisField.finrank 2 (by omega)
  have ec : Fintype.card E = q := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 h (by omega)
  have kc : Fintype.card K = q^m := by rw [Module.card_eq_pow_finrank (K:=E),ec,hdim]
  have hc : c ≤ m*(Fintype.card E-1) := by rw [ec]; exact min_le_right _ _
  obtain ⟨L,hL,cs,prod⟩ := allocate (E:=E) m c hc
  let eb : Module.Basis (Fin m) E K := (Module.finBasis E K).reindex (finCongr hdim)
  have hh' : 0 < Module.finrank PEqualNP.Outside.L_meta_29735_aux.F E := hed.symm ▸ hh
  obtain ⟨C,S,z0,rank,svc,total⟩ := box_family basis bit hb eb L hL t hh'
    (by rwa [hed,hdim]) (by rwa [hed,hdim])
  have cnt : Fintype.card ((i : Fin m) × (L i)) = c := by simpa using cs
  let e := Fintype.equivFinOfCardEq cnt
  refine ⟨fun i => C (e.symm i),S,z0,?_,?_,?_⟩
  · intro i
    have hi := rank (e.symm i)
    rw [hed] at hi
    exact hi
  · intro z hz
    obtain ⟨u,hu⟩ := svc z hz
    refine ⟨e u,?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hu
  · rw [prod,ec,kc] at total
    exact total
end Attain

section Reduced
open MvPolynomial

variable {E : Type} [Field E] [Fintype E]

noncomputable def smallPower (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => n%(q-1)+1

theorem small_le (q n : ℕ) : smallPower q n ≤ n := by
  cases n with
  | zero => rfl
  | succ n => exact Nat.succ_le_succ (Nat.mod_le n _)

theorem small_lt {q : ℕ} (hq : 1 < q) (n : ℕ) : smallPower q n < q := by
  cases n with
  | zero => change 0 < q; omega
  | succ n =>
    change n%(q-1)+1 < q
    have := Nat.mod_lt n (by omega : 0 < q-1)
    omega

theorem small_eval (x : E) (n : ℕ) : x^smallPower (Fintype.card E) n = x^n := by
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hx : x=0
    · subst x; simp [smallPower]
    · simp only [smallPower,pow_succ]
      congr 1
      let q := Fintype.card E
      calc
        x^(n%(q-1)) = x^((q-1)*(n/(q-1))+n%(q-1)) := by
          rw [pow_add,pow_mul,FiniteField.pow_card_sub_one_eq_one x hx,one_pow,one_mul]
        _ = x^n := by rw [Nat.div_add_mod]

noncomputable def reduceExp {m : ℕ} (q : ℕ) (d : Fin m →₀ ℕ) : Fin m →₀ ℕ :=
  d.mapRange (smallPower q) rfl

noncomputable def normalize {m : ℕ} (p : MvPolynomial (Fin m) E) : MvPolynomial (Fin m) E :=
  ∑ d ∈ p.support, monomial (reduceExp (Fintype.card E) d) (p.coeff d)

theorem normalize_eval {m : ℕ} (p : MvPolynomial (Fin m) E) (x : Fin m → E) :
    eval x (normalize p) = eval x p := by
  classical
  conv_rhs => rw [p.as_sum]
  simp only [normalize,map_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_fintype _ _ (by simp)]
  exact Finset.prod_congr rfl (fun i _ => small_eval (x i) (d i))

theorem normalize_degree {m : ℕ} (p : MvPolynomial (Fin m) E) :
    (normalize p).totalDegree ≤ p.totalDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_monomial_le ..).trans
  apply le_trans _ (le_totalDegree hd)
  rw [Finsupp.sum_fintype _ _ (by simp),Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum (fun i _ => small_le _ (d i))

theorem normalize_degreeOf {m : ℕ} (p : MvPolynomial (Fin m) E) (i : Fin m) :
    (normalize p).degreeOf i < Fintype.card E := by
  classical
  apply lt_of_le_of_lt (degreeOf_sum_le ..)
  rw [Finset.sup_lt_iff (by exact Fintype.card_pos)]
  intro d hd
  rw [degreeOf_monomial_eq _ _ (mem_support_iff.mp hd)]
  exact small_lt Fintype.one_lt_card _
end Reduced

section Footprint
open MvPolynomial
open scoped Classical

variable {E : Type} [Field E] [Fintype E]

noncomputable def weight {α : Type} [Fintype α] (f : α → E) : ℕ :=
  ∑ x, if f x ≠ 0 then 1 else 0

theorem weight_eq_card {α : Type} [Fintype α] (f : α → E) :
    weight f = (Finset.univ.filter (fun x => f x ≠ 0)).card := by
  exact_mod_cast Finset.sum_boole (R:=ℕ) (fun x => f x ≠ 0) Finset.univ

theorem weight_cons {m : ℕ} (f : (Fin (m+1) → E) → E) :
    weight f = ∑ y : Fin m → E, weight (fun a => f (Fin.cons a y)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (m+1) => E)
  change (∑ x, if f x ≠ 0 then 1 else 0) = _
  rw [← Equiv.sum_comp e _]
  rw [Fintype.sum_prod_type_right]
  rfl

theorem polynomial_weight (p : Polynomial E) (hp : p ≠ 0) :
    Fintype.card E-p.natDegree ≤ weight (fun a => p.eval a) := by
  classical
  have h : (Finset.univ.filter (fun a => p.eval a = 0)).card ≤ p.natDegree := by
    apply le_trans (Finset.card_le_card (t:=p.roots.toFinset) ?_)
      (p.roots.toFinset_card_le.trans p.card_roots')
    intro a ha
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp ha).2)
  rw [weight_eq_card]
  have eq := Finset.card_filter_add_card_filter_not (s:= (Finset.univ : Finset E)) (p:=fun a => p.eval a=0)
  simp only [Finset.card_univ] at eq
  apply Nat.sub_le_iff_le_add.mpr
  rw [←eq,Nat.add_comm]
  exact Nat.add_le_add_left h _

theorem reduced_footprint {m : ℕ} (p : MvPolynomial (Fin m) E) (hp : p ≠ 0)
    (hr : ∀ i, p.degreeOf i < Fintype.card E) :
    ∃ d : Fin m → ℕ, (∀ i, d i < Fintype.card E) ∧
      (∑ i, d i) ≤ p.totalDegree ∧
      (∏ i, (Fintype.card E - d i)) ≤ weight (fun x => eval x p) := by
  classical
  induction m with
  | zero =>
    refine ⟨Fin.elim0,(fun i => i.elim0),by simp,?_⟩
    rw [p.eq_C_of_isEmpty] at hp ⊢
    simpa [weight, C_ne_zero.mp hp]
  | succ m ih =>
    let P := finSuccEquiv E m p
    let j := P.natDegree
    let A := P.leadingCoeff
    have p_ne : P ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hp
    have hA : A ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr p_ne
    have de : A.totalDegree+j ≤ p.totalDegree := totalDegree_coeff_finSuccEquiv_add_le p j hA
    have jr : j < Fintype.card E := by simpa [j,P,natDegree_finSuccEquiv] using hr 0
    obtain ⟨d,db,ds,dw⟩ := ih A hA (fun i =>
      lt_of_le_of_lt (degreeOf_coeff_finSuccEquiv p i j) (hr i.succ))
    refine ⟨Fin.cons j d,?_,?_,?_⟩
    · exact Fin.cases jr db
    · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ]; omega
    · rw [Fin.prod_univ_succ,weight_cons]
      simp only [Fin.cons_zero,Fin.cons_succ]
      apply le_trans (Nat.mul_le_mul_left _ dw)
      rw [weight,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : eval y A ≠ 0
      · rw [if_pos hy,Nat.mul_one]
        let Q := P.map (eval y)
        have q_ne : Q ≠ 0 := by
          intro hz
          apply hy
          change eval y (P.coeff j) = 0
          rw [←Polynomial.coeff_map,show P.map (eval y) = 0 from hz,Polynomial.coeff_zero]
        have qd : Q.natDegree=j := Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hy
        have h := polynomial_weight Q q_ne
        rw [qd] at h
        simpa only [eval_eq_eval_mv_eval'] using h
      · simp [hy]

theorem grid_footprint {m : ℕ} (p : MvPolynomial (Fin m) E)
    (hp : ∃ w, eval w p ≠ 0) :
    ∃ d : Fin m → ℕ, (∀ i, d i < Fintype.card E) ∧
      (∑ i, d i) ≤ p.totalDegree ∧
      (∏ i, (Fintype.card E - d i)) ≤ weight (fun x => eval x p) := by
  obtain ⟨w,hw⟩ := hp
  have hn : normalize p ≠ 0 := fun hz => hw (by rw [←normalize_eval p w,hz,map_zero])
  obtain ⟨d,hd,hs,hc⟩ := reduced_footprint (normalize p) hn (normalize_degreeOf p)
  exact ⟨d,hd,hs.trans (normalize_degree p),by simpa only [normalize_eval] using hc⟩
end Footprint

section Concentrate
open scoped BigOperators

theorem stack_low (q r b : ℕ) (hl : r+b ≤ q-1) (hq : 1 < q) :
    (q-(r+b))*q ≤ (q-r)*(q-b) := by
  zify [show r+b ≤ q by omega,show r ≤ q by omega,show b ≤ q by omega]
  nlinarith [Int.ofNat_nonneg (r*b)]

theorem stack_high (q r b : ℕ) (hr : r < q) (hb : b < q) (hl : q-1 ≤ r+b) :
    q-(r+b-(q-1)) ≤ (q-r)*(q-b) := by
  have hprod := Nat.zero_le ((q-r-1)*(q-b-1))
  have eq : (q-r)*(q-b) = (q-r-1)*(q-b-1)+(q-r-1)+(q-b-1)+1 := by
    have h : q-r = (q-r-1)+1 := by omega
    have g : q-b = (q-b-1)+1 := by omega
    conv_lhs => rw [h,g]
    ring
  omega

theorem compress {q : ℕ} (hq : 1 < q) :
    ∀ m (d : Fin (m+1) → ℕ), (∀ i, d i < q) →
      ∃ a b u : ℕ, a+u=m ∧ b<q ∧ (∑ i, d i) = a*(q-1)+b ∧
        (q-b)*q^u ≤ ∏ i, (q-d i) := by
  intro m
  induction m with
  | zero =>
    intro d hd
    exact ⟨0,d 0,0,rfl,hd 0,by simp,by simp⟩
  | succ m ih =>
    intro d hd
    let r := d 0
    have hr : r<q := hd 0
    obtain ⟨a,b,u,eq,hb,sum,prod⟩ := ih (fun i => d i.succ) (fun i => hd i.succ)
    rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
    rw [sum]
    by_cases h : r+b ≤ q-1
    · refine ⟨a,r+b,u+1,by omega,by omega,by dsimp [r]; omega,?_⟩
      calc
        _ = ((q-(r+b))*q)*q^u := by rw [pow_succ']; ac_rfl
        _ ≤ ((q-r)*(q-b))*q^u := Nat.mul_le_mul_right _ (stack_low q r b h hq)
        _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ prod
    · refine ⟨a+1,r+b-(q-1),u,by omega,by omega,?_,?_⟩
      · rw [Nat.succ_mul]; change r+_=_; omega
      · calc
          _ ≤ ((q-r)*(q-b))*q^u := Nat.mul_le_mul_right _ (stack_high q r b hr hb (by omega))
          _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ prod

noncomputable def fill (q s i : ℕ) := min (q-1) (s-i*(q-1))

theorem fill_profile (q a b i : ℕ) (hb : b≤q-1) :
    fill q (a*(q-1)+b) i = levelSize q a b i := by
  unfold fill levelSize
  split_ifs with h e
  · have he := Nat.mul_le_mul_right (q-1) (show i+1 ≤ a by omega)
    rw [Nat.succ_mul] at he
    omega
  · subst i; omega
  · have he := Nat.mul_le_mul_right (q-1) (show a+1 ≤ i by omega)
    rw [Nat.succ_mul] at he
    omega

theorem profile_product (q a b u : ℕ) (hq : 1<q) :
    (∏ i : Fin (a+u+1), (q-levelSize q a b i))=(q-b)*q^u := by
  induction a with
  | zero =>
    simp only [Nat.zero_add,Fin.prod_univ_succ]
    have tail (i : Fin u) : levelSize q 0 b i.succ = 0 := by simp [levelSize]
    simp [tail,levelSize]
  | succ a ih =>
    rw [show a+1+u+1=(a+u+1)+1 by omega]
    rw [Fin.prod_univ_succ]
    have tail (i : Fin (a+u+1)) : levelSize q (a+1) b i.succ = levelSize q a b i := by simp [levelSize]
    simp only [Fin.val_zero,tail,ih]
    have head : q-levelSize q (a+1) b 0 = 1 := by simp [levelSize]; omega
    rw [head,one_mul]

theorem extremal_product {m q s : ℕ} (hq : 1<q) (d : Fin m → ℕ)
    (hd : ∀ i, d i < q) (hs : (∑ i, d i) ≤ s) (hc : s ≤ m*(q-1)) :
    let a := s/(q-1)
    let b := s%(q-1)
    q^(m-a)-b*q^(m-a-1) ≤ ∏ i, (q-d i) := by
  intro a b
  have split : a*(q-1)+b=s := by rw [mul_comm]; exact Nat.div_add_mod s _
  have hb : b < q-1 := Nat.mod_lt _ (by omega)
  have ha : a ≤ m := by
    by_contra! hn
    have := Nat.mul_lt_mul_of_pos_right hn (by omega : 0 < q-1)
    omega
  have totals := (level_totals q b hq (by omega) m a ha (by intro e; rw [e] at split; omega)).2
  rw [← totals]
  have fill_eq (i : Fin m) : levelSize q a b i = fill q s i := by
    rw [← split]; exact (fill_profile q a b i (by omega)).symm
  simp only [fill_eq]
  cases m with
  | zero => simp
  | succ m =>
    obtain ⟨A,B,U,eq,hB,sum,bound⟩ := compress hq m d hd
    subst m
    apply le_trans _ bound
    rw [← profile_product q A B U hq]
    apply Finset.prod_le_prod' (fun i _ => ?_)
    rw [← fill_profile q A B i (by omega)]
    apply Nat.sub_le_sub_left
    apply min_le_min_left
    exact Nat.sub_le_sub_right (sum ▸ hs) _
end Concentrate

section Determinants
open MvPolynomial Module LinearMap

variable {E K : Type} [Field E] [Field K] [Algebra E K]
variable {m r : ℕ}

noncomputable def pencil (B : Fin m → Matrix (Fin r) (Fin r) E) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin m) E) := fun a b =>
  MvPolynomial.C ((1 : Matrix (Fin r) (Fin r) E) a b) + ∑ i, X i * MvPolynomial.C (B i a b)

theorem pencil_eval (B : Fin m → Matrix (Fin r) (Fin r) E) (x : Fin m → E) :
    eval x (pencil B).det = (1 + ∑ i, x i • B i).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [pencil,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]

theorem pencil_degree (B : Fin m → Matrix (Fin r) (Fin r) E) : (pencil B).det.totalDegree ≤ r := by
  classical
  have entry (a b : Fin r) : ((pencil B) a b).totalDegree ≤ 1 := by
    apply (totalDegree_add ..).trans
    apply max_le (by simp)
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul ..).trans (by simp)
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_mul ..).trans
  have sign : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin m) E).totalDegree = 0 := by
    rw [← map_intCast (MvPolynomial.C : E →+* MvPolynomial (Fin m) E),totalDegree_C]
  rw [sign,zero_add]
  apply (totalDegree_finsetProd ..).trans
  exact le_trans (Finset.sum_le_sum (fun i _ => entry (σ i) i)) (by simp)

variable [FiniteDimensional E K]

noncomputable def compressMap (C : K →ₗ[E] K) (v : K) : LinearMap.range C →ₗ[E] LinearMap.range C :=
  C.rangeRestrict.comp ((LinearMap.mul E K v).comp (range C).subtype)

theorem compressMap_apply (C : K →ₗ[E] K) (v : K) (y : range C) :
    (compressMap C v y : K) = C (v*y) := rfl

noncomputable def rankPencil (e : Basis (Fin m) E K) (C : K →ₗ[E] K) :=
  let u := Module.finBasis E (range C)
  pencil (fun i => LinearMap.toMatrix u u (-compressMap C (e i)))

theorem rankPencil_zero (e : Basis (Fin m) E K) (C : K →ₗ[E] K) :
    eval (0 : Fin m → E) (rankPencil e C).det = 1 := by
  rw [rankPencil,pencil_eval]
  simp

theorem rankPencil_degree (e : Basis (Fin m) E K) (C : K →ₗ[E] K) :
    (rankPencil e C).det.totalDegree ≤ finrank E (range C) := pencil_degree _

theorem rankPencil_eval (e : Basis (Fin m) E K) (C : K →ₗ[E] K) (v : K) :
    eval (e.equivFun v) (rankPencil e C).det =
      LinearMap.det (LinearMap.id - compressMap C v) := by
  let u := Module.finBasis E (range C)
  rw [rankPencil,pencil_eval,← LinearMap.det_toMatrix u]
  congr 1
  let L : K →ₗ[E] (range C →ₗ[E] range C) :=
    { toFun := fun w => -compressMap C w
      map_add' := by
        intro x y
        ext v
        change -C ((x+y)*v.val) = -C (x*v.val) + -C (y*v.val)
        simp [add_mul,add_comm]
      map_smul' := by
        intro s x
        ext v
        change -C ((s • x)*v.val) = s • -C (x*v.val)
        simp [smul_mul_assoc] }
  let M := (LinearMap.toMatrix u u).toLinearMap.comp L
  have sum := congrArg M (e.sum_repr v)
  simp only [_root_.map_sum,_root_.map_smul] at sum
  calc
    _ = (LinearMap.toMatrix u u) LinearMap.id + M v :=
      congrArg₂ (·+·) (LinearMap.toMatrix_id u).symm sum
    _ = (LinearMap.toMatrix u u) (LinearMap.id + -compressMap C v) :=
      ((LinearMap.toMatrix u u).map_add LinearMap.id (-compressMap C v)).symm
    _ = _ := congrArg (LinearMap.toMatrix u u) (_root_.sub_eq_add_neg LinearMap.id (compressMap C v)).symm

theorem pencil_vanishes (e : Basis (Fin m) E K) (C : K →ₗ[E] K) (z : K) (hz : z ≠ 0)
    (hs : ¬ Function.Injective (LinearMap.mul E K z - C)) :
    eval (e.equivFun z⁻¹) (rankPencil e C).det = 0 := by
  rw [rankPencil_eval,LinearMap.det_eq_zero_iff_ker_ne_bot]
  obtain ⟨x,hx,he⟩ := (singular_iff_slope z C).mp hs
  let y := C.rangeRestrict x
  have hy : y ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact (mul_ne_zero hz hx) (he ▸ this : z*x=0)
  intro empty
  apply hy
  have mem : y ∈ ker (LinearMap.id - compressMap C z⁻¹) := by
    apply sub_eq_zero.mpr
    apply Subtype.ext
    change C x = C (z⁻¹ * C x)
    rw [he,← mul_assoc,inv_mul_cancel₀ hz,one_mul,← he]
  rw [empty] at mem
  exact mem
end Determinants

section Bound
open Module LinearMap MvPolynomial
open scoped Classical

variable {E K : Type} [Field E] [Field K] [Algebra E K]
variable [Fintype E] [FiniteDimensional E K] {m l : ℕ}

theorem total_coverage (e : Basis (Fin m) E K) (maps : Fin l → (K →ₗ[E] K))
    (S : Finset K) (z0 : 0 ∉ S) (budget : ℕ)
    (cost : (∑ i, finrank E (range (maps i))) ≤ budget)
    (hs : ∀ z ∈ S, ∃ i, ¬ Function.Injective (LinearMap.mul E K z - maps i)) :
    let q := Fintype.card E
    let c := min budget (m*(q-1))
    let a := c/(q-1)
    let b := c%(q-1)
    S.card + (q^(m-a)-b*q^(m-a-1)) ≤ q^m := by
  intro q c a b
  let P := ∏ i, (rankPencil e (maps i)).det
  have zero : eval (0 : Fin m → E) P = 1 := by
    dsimp only [P]; rw [_root_.map_prod]; simp only [rankPencil_zero,Finset.prod_const_one]
  have deg : P.totalDegree ≤ budget := (totalDegree_finsetProd ..).trans
    ((Finset.sum_le_sum (fun i _ => rankPencil_degree e (maps i))).trans cost)
  obtain ⟨d,db,ds,dw⟩ := grid_footprint P ⟨0,zero.trans_ne one_ne_zero⟩
  have ce : (∑ i, d i) ≤ c := by
    apply le_min (ds.trans deg)
    calc
      _ ≤ ∑ _ : Fin m, (q-1) := Finset.sum_le_sum (fun i _ => by have := db i; change d i < q at this; omega)
      _ = m*(q-1) := by simp
  have low := extremal_product (q:=q) (s:=c) Fintype.one_lt_card d db ce (min_le_right ..)
  let y : K ≃ (Fin m → E) := (Equiv.inv K).trans e.equivFun.toEquiv
  let good := Finset.univ.filter (fun w : Fin m → E => eval w P ≠ 0)
  have dis : Disjoint (S.map y.toEmbedding) good := by
    apply Finset.disjoint_left.mpr
    intro w hw hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨i,hi⟩ := hs z hz
    have nz : z ≠ 0 := fun eq => z0 (eq ▸ hz)
    apply (Finset.mem_filter.mp hp).2
    change eval (e.equivFun z⁻¹) (∏ j, (rankPencil e (maps j)).det) = 0
    rw [_root_.map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (pencil_vanishes e _ z nz hi)
  have total := Finset.card_le_univ ((S.map y.toEmbedding) ∪ good)
  rw [Finset.card_union_of_disjoint dis,Finset.card_map,Fintype.card_fun,Fintype.card_fin] at total
  rw [weight_eq_card] at dw
  exact (Nat.add_le_add_left (low.trans dw) S.card).trans total
end Bound

end PEqualNP.Outside.L_meta_29735_aux

theorem PEqualNP.Outside.L_meta_29735 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (h m t budget : ℕ), 0 < h → 0 < m →
  let F := ZMod 2
  let E := GaloisField 2 h
  let q := 2^h
  let k := h*m
  let n := k+1
  k-h ≤ 2*t → 2*t < k →
  ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    [FiniteDimensional E K], Module.finrank E K = m →
    ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      let point : Fin n → K := Fin.cases 0 basis
      let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
      let table := fun (C : K →ₗ[E] K) (x y : Fin n) => decide (bit (C (point x) * point y) ≠ 0)
      let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) =>
        ∀ z ∈ S, ∃ i : Fin l,
          fits n n 1 (fun _ x y => xor (mult z x y) (table (C i) x y)) t
      let rk := fun (D : K →ₗ[E] K) => Module.finrank E (LinearMap.range D)
      let c := min budget (m*(q-1))
      let a := c/(q-1)
      let b := c % (q-1)
      let left := q^(m-a) - b*q^(m-a-1)
      (∀ (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K),
        (0 : K) ∉ S → (∑ i : Fin l, rk (C i)) ≤ budget → serves l C S →
        S.card + left ≤ q^m) ∧
      (∃ (C : Fin c → (K →ₗ[E] K)) (S : Finset K),
        (0 : K) ∉ S ∧
        (∀ i : Fin c, rk (C i) = 1 ∧ fits n n 1 (fun _ => table (C i)) ((h+1)/2)) ∧
        serves c C S ∧ S.card + left = q^m) := by
  classical
  intro nonlinear depths fits h m t budget hh hm F E q k n hl hu K _ _ _ _ _ hdim basis bit hb point mult table serves rk c a b left
  constructor
  · intro l maps S z0 cost hs
    letI : Fintype E := Fintype.ofFinite E
    have hed : Module.finrank PEqualNP.Outside.L_meta_29735_aux.F E = h := GaloisField.finrank 2 (by omega)
    have ec : Fintype.card E = q := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 h (by omega)
    let eb : Module.Basis (Fin m) E K := (Module.finBasis E K).reindex (finCongr hdim)
    have hc : CharP K 2 := charP_of_injective_algebraMap (algebraMap PEqualNP.Outside.L_meta_29735_aux.F K).injective 2
    have hh' : 0 < Module.finrank PEqualNP.Outside.L_meta_29735_aux.F E := hed.symm ▸ hh
    have eigen (z : K) (hz : z ∈ S) : ∃ i, ¬ Function.Injective (LinearMap.mul E K z - maps i) := by
      obtain ⟨i,hf⟩ := hs z hz
      refine ⟨i,?_⟩
      have hn : -(maps i) = maps i := by ext x; exact CharTwo.neg_eq _
      rw [sub_eq_add_neg,hn,← PEqualNP.Outside.L_meta_29735_aux.fits_singular basis bit hb _ t hh'
        (by rwa [hed,hdim]) (by rwa [hed,hdim]),PEqualNP.Outside.L_meta_29735_aux.label_add]
      exact hf
    have res := PEqualNP.Outside.L_meta_29735_aux.total_coverage eb maps S z0 budget cost eigen
    dsimp only at res
    rw [ec] at res
    exact res
  · exact PEqualNP.Outside.L_meta_29735_aux.exact_attainment h m t budget hh hm hl hu K hdim basis bit hb

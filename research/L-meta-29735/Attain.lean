import Budget

namespace FieldCoverage

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
  have hed : Module.finrank FieldCoverage.F E = h := GaloisField.finrank 2 (by omega)
  have ec : Fintype.card E = q := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 h (by omega)
  have kc : Fintype.card K = q^m := by rw [Module.card_eq_pow_finrank (K:=E),ec,hdim]
  have hc : c ≤ m*(Fintype.card E-1) := by rw [ec]; exact min_le_right _ _
  obtain ⟨L,hL,cs,prod⟩ := allocate (E:=E) m c hc
  let eb : Module.Basis (Fin m) E K := (Module.finBasis E K).reindex (finCongr hdim)
  have hh' : 0 < Module.finrank FieldCoverage.F E := hed.symm ▸ hh
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

end FieldCoverage

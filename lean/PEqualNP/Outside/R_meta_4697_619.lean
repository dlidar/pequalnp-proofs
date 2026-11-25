import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The generic cover-to-pool statement is shared with R_meta_4697_702.
theorem PEqualNP.Outside.R_meta_4697_619
    (packing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)),
      (∀ v ∈ U, G.degree v ≤ 3) → (∀ a b, G.Adj a b → a ∈ U) →
      (∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c) →
      ∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ 3*T.card ≤ 2*U.card)
    (build : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (D : List (Finset (Fin n))),
        B = P ++ a :: D → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧
          (b.card ≤ 1 ∨ b ∈ D) ∧ (c.card ≤ 1 ∨ c ∈ D)) ∧
      (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
      (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
      B.length + 2 * m ≤ G.edgeSet.ncard + T.card)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      3*(C.size+2) ≤ 3*G.edgeSet.ncard + 2*(Finset.univ \ A).card →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeSet.ncard + T.card ≤ C.size+1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  classical
  intro n G _ A cubic girth separated edge s admissible
  obtain ⟨C, fan, bound, good⟩ := admissible
  let sizes := fun k => ∃ Q : Circuit, FanInTwo Q ∧ circuitFun n Q = graphFun G ∅ ∧ Q.size = k
  have nonempty : ∃ k, sizes k := ⟨C.size, C, fan, funext good, rfl⟩
  obtain ⟨D, hfan, heval, hd⟩ := Nat.find_spec nonempty
  have minimal : IsMinimalCircuit n D := by
    refine ⟨hfan, fun Q fq eqQ => ?_⟩
    rw [hd]
    exact Nat.find_min' nonempty ⟨Q, fq, eqQ.trans heval, rfl⟩
  have ds : D.size ≤ s := (minimal.2 C fan ((funext good).trans heval.symm)).trans bound
  let U : Finset (Fin n) := Finset.univ \ A
  have nod : ∀ a b c, G.Adj a b → G.Adj a c → ¬G.Adj b c := by
    intro a b c ab ac bc
    let w : G.Walk a a := .cons ab (.cons bc (.cons ac.symm .nil))
    have cycle : w.IsCycle := by
      apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simp [w, SimpleGraph.Walk.isPath_def, ab.ne.symm, ac.ne.symm, bc.ne]
      · exact Nat.le_refl 3
    have bad := girth a w cycle
    change 7 ≤ 3 at bad
    omega
  obtain ⟨T,cov,cost⟩ : ∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧
      G.edgeSet.ncard + T.card ≤ D.size+1 := by
    by_cases cheap : 3*(D.size+2) ≤ 3*G.edgeSet.ncard + 2*U.card
    · exact residual n G A D cubic girth separated edge minimal heval cheap
    · obtain ⟨T,tc,tb⟩ := packing n G U (fun v hv => by
          rw [← G.ncard_neighborSet v, cubic v (Finset.mem_sdiff.mp hv).2])
          (fun a b h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,separated a b h⟩) nod
      exact ⟨T,tc,by omega⟩
  obtain ⟨B,m,X,Y,hB,hXY,truth,price⟩ := build n G T cov
  exact ⟨B,m,X,Y,hB,hXY,truth,by omega⟩

import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_7368_619
    (compile : ∀ (gs : List (Bool × ℕ × ℕ)) (o : Fin 3 → ℕ),
    gs.head? = some (false,0,1) → (∀ t, o t < 24+gs.length) →
    ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧ C.gates.head? = some ⟨.or,[0,1]⟩ ∧
      C.output = o 0 ∧ ∀ (s : Finset (Fin 24)) (i : ℕ),
      (C.wires (List.ofFn fun j => decide (j ∈ s))).getD i false = true ↔
      s ∈ (gs.foldl (fun (w : List (Set (Finset (Fin 24)))) g =>
        w ++ [ite (g.1 = true) (w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅) (w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)])
        (List.ofFn fun i : Fin 24 => {s | i ∈ s})).getD i ∅)
    (extend : ∀ (W : Set (Finset (Fin 24))) (P N : Finset (Fin 24) → Prop),
    (∀ a ∈ W, ∀ b, a ⊆ b → b ∈ W) →
    (∀ a, P a → (∀ b, b ⊂ a → ¬ P b) → a ∈ W) →
    (∀ a, N a → (∀ b, a ⊂ b → ¬ N b) → a ∉ W) →
    ∀ a, (P a → a ∈ W) ∧ (N a → a ∉ W))
    (up : ∀ (gs : List (Bool × ℕ × ℕ)) (i : ℕ),
      let w := gs.foldl (fun (w : List (Set (Finset (Fin 24)))) g =>
        w ++ [ite (g.1 = true) (w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅) (w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)])
        (List.ofFn fun i : Fin 24 => {s | i ∈ s});
      ∀ a ∈ w.getD i ∅, ∀ b, a ⊆ b → b ∈ w.getD i ∅)
    (core :
    let D : Finset (Fin 13) := {0,1,3,9};
    let F := fun x : Finset (Fin 24) => ∃ i j : Fin 12,
      (9 : Fin 13).succAbove i + (0 : Fin 13).succAbove j ∈ D ∧
      Fin.castAdd 12 i ∈ x ∧ Fin.natAdd 12 j ∈ x;
    let Q := fun t : Fin 3 => ite (t = 1) ({0,1,3} : Finset (Fin 24)) {15,16,18};
    let P := fun (t : Fin 3) (x : Finset (Fin 24)) => ite (t = 0) (F x) (¬ Disjoint x (Q t));
    let N := fun (t : Fin 3) (x : Finset (Fin 24)) => ¬ F x ∧ (t = 0 ∨ Disjoint x (Q t));
    ∃ (gs : List (Bool × ℕ × ℕ)) (o : Fin 3 → ℕ),
      gs.length ≤ 58 ∧ gs.head? = some (false,0,1) ∧ (∀ t, o t < 24+gs.length) ∧
      let w := gs.foldl (fun (w : List (Set (Finset (Fin 24)))) g =>
        w ++ [ite (g.1 = true) (w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅) (w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)])
        (List.ofFn fun i : Fin 24 => {s | i ∈ s})
      ∀ t a, (P t a → (∀ b, b ⊂ a → ¬ P t b) → a ∈ w.getD (o t) ∅) ∧
        (N t a → (∀ b, a ⊂ b → ¬ N t b) → a ∉ w.getD (o t) ∅))
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 + x3 ∈ x1; have x3 : (Fin (24 : ℕ) → Bool) → Prop := fun (x3 : Fin (24 : ℕ) → Bool) => ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (12 : ℕ)), x2 (Fin.succAbove (9 : Fin (13 : ℕ)) x4) (Fin.succAbove (0 : Fin (13 : ℕ)) x5) ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (58 : ℕ) ∧ x4.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4.output < (24 : ℕ) + x4.size ∧ x5 < (24 : ℕ) + x4.size ∧ x6 < (24 : ℕ) + x4.size ∧ (∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.true ↔ x3 x7) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.false → (x4.wires (List.ofFn x7)).getD x5 Bool.false = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ (x4.wires (List.ofFn x7)).getD x6 Bool.false = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))) := by
  classical
  let D : Finset (Fin 13) := {0,1,3,9}
  let F := fun x : Finset (Fin 24) => ∃ i j : Fin 12,
      (9 : Fin 13).succAbove i + (0 : Fin 13).succAbove j ∈ D ∧
      Fin.castAdd 12 i ∈ x ∧ Fin.natAdd 12 j ∈ x
  let Q := fun t : Fin 3 => ite (t = 1) ({0,1,3} : Finset (Fin 24)) {15,16,18}
  let P := fun (t : Fin 3) (x : Finset (Fin 24)) => ite (t = 0) (F x) (¬ Disjoint x (Q t))
  let N := fun (t : Fin 3) (x : Finset (Fin 24)) => ¬ F x ∧ (t = 0 ∨ Disjoint x (Q t))
  obtain ⟨gs,o,sz,hd,bd,ok⟩ := core
  obtain ⟨C,m,cs,ch,co,read⟩ := compile gs o hd bd
  refine ⟨C,o 1,o 2,m,cs ▸ sz,ch,by rw [cs,co]; exact bd 0,by rw [cs]; exact bd 1,by rw [cs]; exact bd 2,?_,?_⟩
  all_goals
    intro x
    let a : Finset (Fin 24) := Finset.univ.filter fun i => x i = true
    have ax (i) : i ∈ a ↔ x i = true := by simp [a]
    have eq : (fun j => decide (j ∈ a)) = x := by funext j; simp [a]
    have val (t : Fin 3) := extend _ (P t) (N t) (up gs (o t))
      (fun z => (ok t z).1) (fun z => (ok t z).2) a
    have rd := fun t : Fin 3 => read a (o t)
    simp only [eq] at rd
  · change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
    rw [co,rd 0]
    constructor
    · intro h
      by_contra q
      apply (val 0).2 ?_ h
      simpa [N,F,D,ax] using q
    · intro h
      apply (val 0).1
      simpa [P,F,D,ax] using h
  · intro neg
    have no : ¬ F a := by
      intro hf
      have yes := (rd 0).mpr ((val 0).1 (by simpa [P] using hf))
      change (C.wires (List.ofFn x)).getD C.output false = false at neg
      rw [co,yes] at neg
      exact Bool.noConfusion neg
    have monitor (t : Fin 3) (ht : t ≠ 0) :
        (C.wires (List.ofFn x)).getD (o t) false = decide (¬ Disjoint a (Q t)) := by
      apply Bool.eq_iff_iff.mpr
      rw [rd,decide_eq_true_eq]
      constructor
      · intro yes dis
        exact (val t).2 ⟨no,Or.inr dis⟩ yes
      · intro yes
        exact (val t).1 (by simpa [P,ht] using yes)
    constructor
    · rw [monitor 1 (by decide)]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      change ¬ Disjoint a ({0,1,3} : Finset (Fin 24)) ↔ _
      rw [Finset.not_disjoint_iff]
      simp only [Finset.mem_insert,Finset.mem_singleton,Bool.or_eq_true]
      constructor
      · rintro ⟨v,hv,rfl | rfl | rfl⟩
        · exact Or.inl (Or.inl ((ax _).mp hv))
        · exact Or.inl (Or.inr ((ax _).mp hv))
        · exact Or.inr ((ax _).mp hv)
      · rintro ((h | h) | h)
        · exact ⟨_,(ax _).mpr h,Or.inl rfl⟩
        · exact ⟨_,(ax _).mpr h,Or.inr (Or.inl rfl)⟩
        · exact ⟨_,(ax _).mpr h,Or.inr (Or.inr rfl)⟩
    · rw [monitor 2 (by decide)]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      change ¬ Disjoint a ({15,16,18} : Finset (Fin 24)) ↔ _
      rw [Finset.not_disjoint_iff]
      simp only [Finset.mem_insert,Finset.mem_singleton,Bool.or_eq_true]
      constructor
      · rintro ⟨v,hv,rfl | rfl | rfl⟩
        · exact Or.inl (Or.inl ((ax _).mp hv))
        · exact Or.inl (Or.inr ((ax _).mp hv))
        · exact Or.inr ((ax _).mp hv)
      · rintro ((h | h) | h)
        · exact ⟨_,(ax _).mpr h,Or.inl rfl⟩
        · exact ⟨_,(ax _).mpr h,Or.inr (Or.inl rfl)⟩
        · exact ⟨_,(ax _).mpr h,Or.inr (Or.inr rfl)⟩

import PEqualNP.Defs

-- The peeling induction follows R_meta_2974_1. The dense case restricts to a pencil.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2974_619
    (pin : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n),
      PEqualNP.TopForm.IsAO2 n C →
      (∃ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) ∧
        PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) →
      PEqualNP.MetaComplexity.circuitFun n C (fun i => decide (i = v)) = false →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
        (∀ x, PEqualNP.MetaComplexity.circuitFun n D x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧
        (∀ x, x v = false → PEqualNP.MetaComplexity.circuitFun n D x = PEqualNP.MetaComplexity.circuitFun n C x) ∧
        ∀ (s : ℕ → Bool) (a b : ℕ), v.val ≠ a → v.val ≠ b →
          PEqualNP.ReadK.lineSingle D n s a b = PEqualNP.ReadK.lineSingle C n s a b)
    (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 → (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C →
      let hits := fun (v : Fin (N + N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (fun i => decide (hits i e)) = true ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
      (∀ B : Finset (Fin N), B.card ≤ q →
        PEqualNP.MetaComplexity.circuitFun (N+N) C
          (Fin.append (fun a => decide (∀ l ∈ B, ¬I a l)) (fun l => decide (l ∈ B))) = false) →
      (∃ (p : Fin N) (T : Finset (Fin N)), T.card = 25 ∧ (∀ l ∈ T, I p l) ∧
        (∀ l ∈ T, 24 ≤ Fintype.card {a : Fin N // a ≠ p ∧ (a,l) ∈ E}) ∧
        ∀ A B : Finset (Fin N), B ⊆ T →
          (∀ a ∈ A, a ≠ p ∧ ∃ l ∈ T, (a,l) ∈ E) →
          (PEqualNP.MetaComplexity.circuitFun (N+N) C
            (Fin.append (fun a => decide (a ∈ A)) (fun l => decide (l ∈ B))) = true ↔
            ∃ a ∈ A, ∃ l ∈ B, (a,l) ∈ E)) → E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  intro q N I inst C hq hN hcol huniq hao hsound
  let hits := fun (v : Fin (N + N)) (e : Fin N × Fin N) => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
  let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) => decide (hits i e)
  let single := fun (v i : Fin (N + N)) => decide (i = v)
  let sound := fun (D : PEqualNP.CircuitLowerBounds.Circuit) => ∀ z : Fin (N + N) → Bool,
    Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    PEqualNP.MetaComplexity.circuitFun (N + N) D z = false
  let bad := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (e : Fin N × Fin N) =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) D (pair e) = true ∧
      PEqualNP.ReadK.lineSingle D (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      PEqualNP.ReadK.lineSingle D (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.isLt
    omega
  have singleton_off (D) (hs : sound D) (w : Fin (N + N)) :
      PEqualNP.MetaComplexity.circuitFun (N + N) D (single w) = false := by
    apply hs
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, decide_eq_true_eq] at ha hb
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha.trans hb.symm)))
    · rintro ⟨p, l, _, hp, hl⟩
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  let wiresStep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
      (w ++ [b]).getD m false = b := by
    subst hm
    simp [List.getD_eq_getElem?_getD]

  have monotone_foldl_wiresStep (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (hM : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
      (w1 w2 : List Bool) (hlen : w1.length = w2.length)
      (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
      ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
        (gs.foldl wiresStep w2).getD k false = true := by
    induction gs generalizing w1 w2 with
    | nil => exact hle
    | cons g gs ih =>
      have hg : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        simpa using hM g List.mem_cons_self
      have hM' : ∀ g' ∈ gs, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) :=
        fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
      apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
      · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
      · intro k hk
        by_cases hlt : k < w1.length
        · have hlt2 : k < w2.length := hlen ▸ hlt
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hle k hk
        · by_cases heq : k = w1.length
          · subst heq
            have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
              simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
            dsimp only [wiresStep]
            rw [getD_append_last_eq w2 _ w1.length hlen.symm]
            rcases hg with hand | hor
            · rw [hand] at hk1 ⊢
              change (g.inputs.map fun i => w1.getD i false).all id = true at hk1
              change (g.inputs.map fun i => w2.getD i false).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
              intro i hi
              exact hle i (hk1 i hi)
            · rw [hor] at hk1 ⊢
              change (g.inputs.map fun i => w1.getD i false).any id = true at hk1
              change (g.inputs.map fun i => w2.getD i false).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
              obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
              exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
          · have hge : (wiresStep w1 g).length ≤ k := by
              simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
              omega
            rw [getD_ge_length _ k hge] at hk
            cases hk

  have mono (D : PEqualNP.CircuitLowerBounds.Circuit) (hAO : PEqualNP.TopForm.IsAO2 (N+N) D)
      (x y : Fin (N+N) → Bool) (le : ∀ i, x i = true → y i = true) :
      PEqualNP.MetaComplexity.circuitFun _ D x = true →
      PEqualNP.MetaComplexity.circuitFun _ D y = true := by
    apply monotone_foldl_wiresStep D.gates _ _ _ (by simp) _ D.output
    · intro g hg
      exact hAO.1 g hg
    · intro z
      by_cases hz : z < N+N
      · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hz),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hz),
            List.getElem_ofFn,List.getElem_ofFn]
        exact le ⟨z,hz⟩
      · simp [List.getD_eq_getElem?_getD,hz]
  have peel : ∀ k (D : PEqualNP.CircuitLowerBounds.Circuit), D.size = k →
      PEqualNP.TopForm.IsAO2 (N + N) D → sound D → ∀ E : Finset (Fin N × Fin N),
      (∀ e ∈ E, bad D e) → E.card ≤ 24 * D.size := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hsize hAO hs E hE
      by_cases dense : ∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card
      · by_cases empty : E = ∅
        · simp [empty]
        obtain ⟨⟨p,l₀⟩,e₀⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        let row := Finset.univ.filter (fun l : Fin N => (p,l) ∈ E)
        have degP := dense (p,l₀) e₀ (Fin.castAdd N p) (Or.inl rfl)
        have liftP : E.filter (hits (Fin.castAdd N p)) ⊆ row.image (fun l => (p,l)) := by
          rintro ⟨a,l⟩ hm
          obtain ⟨mem,h|h⟩ := Finset.mem_filter.mp hm
          · have eq : p = a := Fin.ext (congrArg (fun i : Fin (N+N) => i.val) h)
            subst a
            exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,rfl⟩
          · exact (separate _ _ h).elim
        have big := (Finset.card_le_card liftP).trans Finset.card_image_le
        obtain ⟨T,hsub,hsize⟩ := Finset.exists_subset_card_eq (s := row) (show 25 ≤ row.card by omega)
        have pencil (l) (hl : l ∈ T) : I p l := (hE _ (Finset.mem_filter.mp (hsub hl)).2).1
        apply core q N I D E hq hN hcol huniq hAO hE dense
        · intro B size
          apply hs
          · rw [Fintype.card_subtype]
            simp only [Fin.append_right, decide_eq_true_eq]
            simpa using size
          · rintro ⟨a,l,h,ha,hl⟩
            simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq] at ha hl
            exact ha l hl h
        refine ⟨p,T,hsize,pencil,?_,?_⟩
        · intro l hl
          have degL := dense (p,l) (Finset.mem_filter.mp (hsub hl)).2 (Fin.natAdd N l) (Or.inr rfl)
          let col := Finset.univ.filter (fun a : Fin N => (a,l) ∈ E)
          have liftL : E.filter (hits (Fin.natAdd N l)) ⊆ col.image (fun a => (a,l)) := by
            rintro ⟨a,t⟩ hm
            obtain ⟨mem,h|h⟩ := Finset.mem_filter.mp hm
            · exact (separate _ _ h.symm).elim
            · have eq : l = t := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
              subst t
              exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,rfl⟩
          have bigL := (Finset.card_le_card liftL).trans Finset.card_image_le
          have rm : col.erase p = Finset.univ.filter (fun a : Fin N => a ≠ p ∧ (a,l) ∈ E) := by
            ext a; simp [col]
          rw [Fintype.card_subtype,←rm,Finset.card_erase_of_mem (show p ∈ col by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hsub hl)).2⟩)]
          omega
        intro A B BT leaves
        have hT : T.card ≤ q := by omega
        let x : Fin (N+N) → Bool := Fin.append (fun a => decide (a ∈ A)) (fun l => decide (l ∈ B))
        change PEqualNP.MetaComplexity.circuitFun _ D x = true ↔ _
        have count : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q := by
          rw [Fintype.card_subtype]
          simp only [x, Fin.append_right, decide_eq_true_eq]
          simpa using (Finset.card_le_card BT).trans hT
        constructor
        · intro yes
          by_contra no
          have zero := hs x count (by
            rintro ⟨a,l,incident,ha,hl⟩
            have ma : a ∈ A := by simpa only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq] using ha
            have ml : l ∈ B := by simpa only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq] using hl
            obtain ⟨ne,t,ht,edge⟩ := leaves a ma
            obtain ⟨u,_,only⟩ := huniq a p ne
            have eq : l = t := (only l ⟨incident,pencil _ (BT ml)⟩).trans
              (only t ⟨(hE _ edge).1,pencil _ ht⟩).symm
            exact no ⟨a,ma,l,ml,eq.symm ▸ edge⟩)
          rw [zero] at yes
          contradiction
        · rintro ⟨a,ma,l,ml,edge⟩
          have acc := (hE _ edge).2.1
          apply mono D hAO (pair (a,l)) x _ acc
          intro i hi
          rcases of_decide_eq_true hi with rfl | rfl
          · simpa only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq] using ma
          · simpa only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq] using ml
      push Not at dense
      obtain ⟨e, he, v, hv, hdeg⟩ := dense
      have acc := (hE e he).2.1
      have essential : ∃ x y : Fin (N + N) → Bool, (∀ i, i ≠ v → x i = y i) ∧
          PEqualNP.MetaComplexity.circuitFun (N + N) D x ≠ PEqualNP.MetaComplexity.circuitFun (N + N) D y := by
        rcases hv with rfl | rfl
        · refine ⟨pair e, single (Fin.natAdd N e.2), ?_, ?_⟩
          · intro i hi; simp only [pair, hits, single, hi, false_or]
          · rw [acc, singleton_off D hs]; decide
        · refine ⟨pair e, single (Fin.castAdd N e.1), ?_, ?_⟩
          · intro i hi; simp only [pair, hits, single, hi, or_false]
          · rw [acc, singleton_off D hs]; decide
      obtain ⟨D', hAO', hlt, hdom, hsame, hparts⟩ := pin _ D v hAO essential (singleton_off D hs v)
      have hs' : sound D' := by
        intro z hcount hno
        apply Bool.eq_false_iff.mpr
        intro h
        exact Bool.noConfusion ((hdom z h).symm.trans (hs z hcount hno))
      let F := E.filter fun f => ¬ hits v f
      have keep : ∀ f ∈ F, bad D' f := by
        intro f hf
        obtain ⟨hfE, hmiss⟩ := Finset.mem_filter.mp hf
        obtain ⟨hi, hyes, hline, hpoint⟩ := hE f hfE
        have hleft : v.val ≠ f.1.val := fun eq => hmiss (Or.inl (Fin.ext eq))
        have hright : v.val ≠ N + f.2.val := fun eq => hmiss (Or.inr (Fin.ext eq))
        exact ⟨hi, (hsame (pair f) (by simp [pair, hmiss])).trans hyes,
          (hparts _ _ _ hleft hright).trans hline, (hparts _ _ _ hleft hright).trans hpoint⟩
      have small := ih D'.size (by omega) D' rfl hAO' hs' F keep
      have split := Finset.card_filter_add_card_filter_not (s := E) (hits v)
      change (E.filter (hits v)).card + F.card = E.card at split
      omega
  rw [Fintype.card_subtype]
  exact peel C.size C rfl hao hsound _ (fun _ he => (Finset.mem_filter.mp he).2)

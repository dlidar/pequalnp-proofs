import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.GenericRejection

-- Move the marked flag through a Fano incidence automorphism. Only one pair of
-- marked inputs remains in the circuit-to-formula question.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_5777_619
    (transport : ∀ (C : Circuit) (p l : Fin 7), p ∈ fanoLines l → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    ComputesIncidence fanoLines C → ∃ (D : Circuit) (e : Fin 14 ≃ Fin 14),
    e 0 = Fin.castAdd 7 p ∧ e 7 = Fin.natAdd 7 l ∧ D.size = C.size ∧ IsAO2 14 D ∧
    (∀ g ∈ D.gates, g.inputs.Nodup) ∧ ComputesIncidence fanoLines D ∧
    D.lineDeg 14 {0} = C.lineDeg 14 {p.val} ∧ D.lineDeg 14 {7} = C.lineDeg 14 {7+l.val} ∧
    ∀ x : Fin 14 → Bool, D.eval (List.ofFn (x ∘ e)) = C.eval (List.ofFn x))
    (fixed : have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x4 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {0} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {7} → ∃ (x14 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x14 ∧ x14.leaves ≤ (28 : ℕ) ∧ (∀ (x15 : Fin (14 : ℕ) → Bool), x14.eval x15 = x4.eval (List.ofFn x15)) ∧ (2 : ℕ) ≤ x3 (0) x14 ∧ (2 : ℕ) ≤ x3 (7) x14) :
    have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x4 → x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x14 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x14 ∧ x14.leaves ≤ (28 : ℕ) ∧ (∀ (x15 : Fin (14 : ℕ) → Bool), x14.eval x15 = x4.eval (List.ofFn x15)) ∧ (2 : ℕ) ≤ x3 (↑x5) x14 ∧ (2 : ℕ) ≤ x3 ((7 : ℕ) + ↑x6) x14 := by
  intro valid degProp deg C p l hs ha hn hI hflag hp hl
  obtain ⟨D,e,ep,el,sz,ao,nd,cmp,dp,dl,heval⟩ := transport C p l hflag ha hn hI
  obtain ⟨f,hf,hsize,hfun,hp0,hl7⟩ := fixed D (sz ▸ hs) ao nd cmp (dp ▸ hp) (dl ▸ hl)
  let rename : DMFormula 14 → DMFormula 14 := DMFormula.rec (fun i b => DMFormula.lit (e i) b)
    (fun _ _ a b => .and a b) (fun _ _ a b => .or a b)
  have litback (a : DMFormula 14) (i : Fin 14) (h : rename a = .lit i true) :
      a = .lit (e.symm i) true := by
    cases a with
    | lit j b =>
      change DMFormula.lit (e j) b = .lit i true at h
      cases h
      simp
    | and a b => cases h
    | or a b => cases h
  have keep (a : DMFormula 14) (h : degProp a) : degProp (rename a) := by
    induction a with
    | lit i b => exact h
    | and a b ia ib | or a b ia ib =>
      obtain ⟨ha',hb',hd⟩ := h
      refine ⟨ia ha',ib hb',?_⟩
      rintro ⟨i,hi,hj⟩
      exact hd ⟨e.symm i,litback a i hi,litback b i hj⟩
  have leaves (a : DMFormula 14) : (rename a).leaves = a.leaves := by
    induction a with
    | lit => rfl
    | and a b ia ib | or a b ia ib => exact congrArg₂ (· + ·) ia ib
  have eval (a : DMFormula 14) (x : Fin 14 → Bool) : (rename a).eval x = a.eval (x ∘ e) := by
    induction a with
    | lit => rfl
    | and a b ia ib => exact congrArg₂ (· && ·) ia ib
    | or a b ia ib => exact congrArg₂ (· || ·) ia ib
  have degree (a : DMFormula 14) (i : Fin 14) : deg (e i).val (rename a) = deg i.val a := by
    induction a with
    | lit j b =>
      change (if (e j).val = (e i).val then 1 else 0) = (if j.val = i.val then 1 else 0)
      by_cases h : j = i
      · subst j; simp
      · have h1 : (e j).val ≠ (e i).val := fun z => h (e.injective (Fin.ext z))
        have h2 : j.val ≠ i.val := fun z => h (Fin.ext z)
        simp [h1,h2]
    | and a b ia ib => exact congrArg₂ (· + ·) ia ib
    | or a b ia ib => exact congrArg₂ max ia ib
  refine ⟨rename f,keep f hf,(leaves f) ▸ hsize,fun x => (eval f x).trans ((hfun _).trans (heval x)),?_,?_⟩
  · have z := degree f 0
    rw [ep] at z
    exact z.symm ▸ hp0
  · have z := degree f 7
    rw [el] at z
    exact z.symm ▸ hl7

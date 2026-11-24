import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1924_619
  (sibling : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size)
  (lastGate : ∀ C D : Circuit, Monotone2 C → FanInTwo D → 0 < D.size → D.output = 10 + C.size + D.size → (∀ x : Fin 9 → Bool, let w := (C.wires (List.ofFn x ++ [x 0 || x 4])); D.eval (w ++ [!w.getD C.output false]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 14 ≤ C.size + D.size) :
  ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := x1.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]);           x2.eval (x6 ++ [!x6.getD x1.output Bool.false]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size + x2.size := by
  intro C D hC hD ok
  let f := (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
  let inp (x : Fin 9 → Bool) := (List.ofFn x ++ [x 0 || x 4])
  have mono : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 14 ≤ C.size := by
    intro A hA hval
    apply Nat.le_trans (by decide : 14 ≤ 15) (sibling A hA ?_)
    intro m hm
    dsimp only
    rw [hval]
    let check (n : ℕ) := decide (f (fun i => n.testBit i.val) = decide (n ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ)))
    have allRows : ([3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402] : List ℕ).all check = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp allRows m hm)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  have len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp [step] <;> omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih _ (by simp [step] <;> omega)]
      exact List.getD_append _ _ _ _ h
  let w (x : Fin 9 → Bool) := C.wires (inp x)
  let v (x : Fin 9 → Bool) := w x ++ [!(w x).getD C.output false]
  have lw (x) : (w x).length = 10 + C.size := by
    change (run C.gates (inp x)).length = _
    rw [len]; change (List.ofFn x ++ [_]).length + C.gates.length = 10 + C.gates.length; simp
  have lv (x) : (v x).length = 11 + C.size := by simp [v, lw] <;> omega
  change ∀ x, (run D.gates (v x)).getD D.output false = f x at ok
  by_cases early : D.output < 10 + C.size
  · let A : Circuit := ⟨C.gates, D.output⟩
    have bound := mono A hC (by
      intro x
      change (w x).getD D.output false = f x
      rw [← ok x, keep _ _ _ (by rw [lv]; omega)]
      exact (List.getD_append _ _ _ _ (by rw [lw]; exact early)).symm)
    change 14 ≤ C.size at bound
    omega
  by_cases mid : D.output = 10 + C.size
  · have neg (x) : (!(w x).getD C.output false) = f x := by
      rw [← ok x, keep _ _ _ (by rw [lv]; omega)]
      change _ = (w x ++ [_]).getD D.output false
      rw [List.getD_append_right _ _ _ _ (by rw [lw]; omega), lw, mid, Nat.sub_self]
      rfl
    have upward (gs : List Gate) (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (a b : List Bool) (hab : a.length = b.length)
        (ord : ∀ i, a.getD i false = true → b.getD i false = true) :
        ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
      induction gs generalizing a b with
      | nil => exact ord
      | cons g gs ih =>
        apply ih (fun t ht => hm t (List.mem_cons_of_mem _ ht)) (step a g) (step b g) (by simp [step, hab])
        intro i hi
        by_cases h : i < a.length
        · rw [List.getD_append _ _ _ _ h] at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append _ _ _ _ (by omega)]
          exact ord i hi
        · change (a ++ [_]).getD i false = true at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), ← hab]
          cases hi' : i - a.length with
          | succ k => simp [hi'] at hi
          | zero =>
            rw [hi'] at hi
            change g.op.eval _ = true at hi ⊢
            rcases hm g (by simp) with hand | hor
            · rw [hand] at hi ⊢
              change (g.inputs.map _).all id = true at hi ⊢
              simp only [List.all_map, List.all_eq_true, Function.comp_apply, id] at hi ⊢
              exact fun i h => ord i (hi i h)
            · rw [hor] at hi ⊢
              change (g.inputs.map _).any id = true at hi ⊢
              simp only [List.any_map, List.any_eq_true, Function.comp_apply, id] at hi ⊢
              obtain ⟨j, hj, val⟩ := hi
              exact ⟨j, hj, ord j val⟩
    have lo := neg (fun _ => false)
    have hi := neg (fun _ => true)
    change (!(w _).getD C.output false) = false at lo
    change (!(w _).getD C.output false) = true at hi
    have rises := upward C.gates (fun g hg => (hC g hg).1)
      (inp (fun _ => false)) (inp (fun _ => true)) rfl (by
        intro i h
        change (List.replicate 10 false).getD i false = true at h
        rw [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] at h
        contradiction) C.output
    change (w _).getD C.output false = true → (w _).getD C.output false = true at rises
    have hz : (w (fun _ => false)).getD C.output false = true := by
      cases e : (w (fun _ => false)).getD C.output false
      · rw [e] at lo; contradiction
      · rfl
    have ht := rises hz
    rw [ht] at hi
    contradiction
  by_cases valid : D.output < 11 + C.size + D.gates.length
  · let n := D.output - (10 + C.size)
    have hn : n ≤ D.gates.length := by dsimp [n]; omega
    let T : Circuit := ⟨D.gates.take n, D.output⟩
    have ts : T.size = n := by change (D.gates.take n).length = n; simp [Nat.min_eq_left hn]
    have lb := lastGate C T hC (fun g hg => hD g (List.mem_of_mem_take hg)) (by rw [ts]; dsimp [n]; omega)
      (by change D.output = 10 + C.size + T.size; rw [ts]; dsimp [n]; omega) (by
        intro x
        change (run (D.gates.take n) (v x)).getD D.output false = f x
        rw [← ok x]
        conv_rhs => rw [← List.take_append_drop n D.gates]
        simp only [run, List.foldl_append]
        change _ = (run (D.gates.drop n) (run (D.gates.take n) (v x))).getD D.output false
        exact (keep _ _ _ (by rw [len, lv, List.length_take, Nat.min_eq_left hn]; dsimp [n]; omega)).symm)
    rw [ts] at lb
    change 14 ≤ C.size + D.gates.length
    omega
  · have h := ok (fun _ => true)
    rw [List.getD_eq_default _ _ (by rw [len, lv]; omega)] at h
    contradiction

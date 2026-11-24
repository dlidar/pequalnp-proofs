import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The eight-vertex child is the statement of L_meta_1664.
theorem PEqualNP.Outside.R_meta_3865_619
    (low : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
    (pin : let reader := fun (g : Gate) => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 9 || i == 10)
      let pinned := fun (x : Fin 8 → Bool) => [false,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3,true,true]
      ∀ C : Circuit, FanInTwo C → 2 ≤ C.gates.countP reader →
      (∃ x, C.eval (pinned x) = false) →
      ∃ R : Circuit, FanInTwo R ∧ R.size + 2 ≤ C.size ∧ ∀ x, R.eval (List.ofFn x) = C.eval (pinned x))
    (one : let reader := fun (g : Gate) => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 9 || i == 10)
      let z := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)
      ∀ (j : Fin 8), (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 4) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → C.gates.countP reader ≤ 1 →
      (∀ x, C.eval ((fun (x : Fin 8 → Bool) => [false,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3,true,true]) x) = z x) →
      ∃ x : Fin 8 → Bool, C.eval [true,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3,false,x j] ≠
        (z x || x 0 || x 6 || x 7)) :
    ∀ (x1 : List ℕ),   x1 = [(9 : ℕ), (1 : ℕ)] ∨ x1 = [(9 : ℕ), (2 : ℕ)] ∨ x1 = [(9 : ℕ), (3 : ℕ)] ∨ x1 = [(9 : ℕ), (4 : ℕ)] ∨ x1 = [(9 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro ks allowed C fan size
  by_contra! good
  let z := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)
  let G := fun (x6 : Fin 9 → Bool) => (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
  let y := fun (b : Bool) (x : Fin 8 → Bool) (i : Fin 9) =>
    [b,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3].getD i false
  let base := fun (b : Bool) (x : Fin 8 → Bool) => [b,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3,!b]
  have layout : ∀ b x, List.ofFn (y b x) ++ [!(y b x 0)] = base b x := fun _ _ => rfl
  have gf : ∀ x, G (y false x) = z x := by
    intro x
    change ((false && x 0 || x 0 && x 1 || x 1 && x 2 || x 2 && x 6 || x 6 && false || false && x 7 || x 0 && x 4 || x 1 && x 5 || x 2 && x 3 || x 7 && x 5 || x 4 && x 3 || x 3 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7))
    simp [Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  have gt : ∀ x, G (y true x) = (z x || x 0 || x 6 || x 7) := by
    intro x
    change ((true && x 0 || x 0 && x 1 || x 1 && x 2 || x 2 && x 6 || x 6 && true || true && x 7 || x 0 && x 4 || x 1 && x 5 || x 2 && x 3 || x 7 && x 5 || x 4 && x 3 || x 3 && x 7)) = (((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) || x 0 || x 6 || x 7)
    simp [Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  obtain ⟨k,j,hks,hj,idx⟩ : ∃ (k : ℕ) (j : Fin 8), ks = [9,k] ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 4) ∧
      ∀ b x, (base b x).getD k false = x j := by
    rcases allowed with h|h|h|h|h
    · exact ⟨1,0,h,by decide,fun _ _ => rfl⟩
    · exact ⟨2,1,h,by decide,fun _ _ => rfl⟩
    · exact ⟨3,2,h,by decide,fun _ _ => rfl⟩
    · exact ⟨4,6,h,by decide,fun _ _ => rfl⟩
    · exact ⟨6,4,h,by decide,fun _ _ => rfl⟩
  subst ks
  have ev' (b : Bool) (x : Fin 8 → Bool) : C.eval (base b x ++ [!b || x j]) = G (y b x) := by
    have h := not_ne_iff.mp (good (y b x))
    change C.eval ((List.ofFn (y b x) ++ [!(y b x 0)]) ++ [GateOp.or.eval ([9,k].map _)]) = G (y b x) at h
    rw [layout] at h
    have disj (a d : Bool) : GateOp.or.eval [a,d] = (a || d) := by cases a <;> cases d <;> rfl
    change C.eval (base b x ++ [GateOp.or.eval [(base b x).getD 9 false, (base b x).getD k false]]) = G (y b x) at h
    rw [disj,idx] at h
    exact h
  let pinned := fun (x : Fin 8 → Bool) => [false,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3,true,true]
  have hf (x) : C.eval (pinned x) = z x := (ev' false x).trans (gf x)
  let reader := fun (g : Gate) => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 9 || i == 10)
  by_cases two : 2 ≤ C.gates.countP reader
  · obtain ⟨R, rfan, smaller, computes⟩ := pin C fan two ⟨fun _ => false, hf (fun _ => false)⟩
    apply low
    exact ⟨R,rfan,by omega,fun x => (computes x).trans (hf x)⟩
  · obtain ⟨x,hx⟩ := one j hj C fan size (show C.gates.countP reader ≤ 1 by omega) hf
    exact hx ((ev' true x).trans (gt x))

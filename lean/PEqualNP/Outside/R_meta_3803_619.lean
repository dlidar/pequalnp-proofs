import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_3803_619
    (packing : ∀ (k : ℕ) (b : Bool) (C : Circuit), Monotone2 C → ∀ (r : Fin k → List Bool),
      (∀ i, C.eval (r i) = b) → (∀ i j, i < j → ∃ z : List Bool, (r i).length = (r j).length ∧ (r i).length = z.length ∧ (∀ a : ℕ, (r i).getD a false = b → (r j).getD a false = b → z.getD a false = b) ∧ C.eval z ≠ b) → k ≤ 2^(C.gates.filter (fun g => (g.inputs.length == 2) && (g.op.eval [true,false] == b))).length)
    (rows : ∀ (C : Circuit), RightOnIncidentPairs singerLines3 C → (∀ Q, IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) → ∀ b : Bool,
      ∃ r : Fin (if b then 52 else 234) → List Bool, (∀ i, C.eval (r i) = b) ∧ (∀ i j, i < j → ∃ z : List Bool, (r i).length = (r j).length ∧ (r i).length = z.length ∧ (∀ a : ℕ, (r i).getD a false = b → (r j).getD a false = b → z.getD a false = b) ∧ C.eval z ≠ b))
    (core : ∀ (C : Circuit), Monotone2 C → ReadsBack 26 C → RightOnIncidentPairs singerLines3 C → (∀ Q, IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
      (∀ b : Bool, (if b then 6 else 8) ≤ (C.gates.filter (fun g => (g.inputs.length == 2) && (g.op.eval [true,false] == b))).length) → 64 ≤ C.size) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → (63 : ℕ) ≤ x6.size := by

  intro D P N good spec C s hs mono back fit
  let A : Circuit := ⟨⟨.or,s⟩ :: C.gates,C.output⟩
  have gd (B : Circuit) (j : ℕ) : gateAt B j = B.gates.getD j ⟨.or,[]⟩ := rfl
  have sd (B : Circuit) : B.size = B.gates.length := rfl
  have incDef (X Y : Finset (Fin 13)) : incidenceInput X Y =
    List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) := rfl
  have missDef (Q : Finset (Fin 13)) : missLines singerLines3 Q =
    Finset.univ.filter (fun l => Disjoint (singerLines3 l) Q) := rfl
  have sLen : s.length ≤ 2 ∧ ∀ i ∈ s, i < 26 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hm : Monotone2 A := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hh
    · exact ⟨Or.inr rfl,sLen.1⟩
    · exact mono g hh
  have hb : ReadsBack 26 A := by
    intro j hj i hi
    cases j with
    | zero => exact sLen.2 i (by simpa [gd,A,List.getD_eq_getElem?_getD] using hi)
    | succ j =>
      have hj' : j < C.gates.length := by simpa [sd,A] using hj
      have hh := back ⟨j,hj'⟩ i (by simpa [gd,A,List.getD_eq_getElem?_getD,hj'] using hi)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have ev (x : List Bool) : A.eval x = C.eval (x ++ [s.any fun j => x.getD j false]) := by
    change C.eval (x ++ [(s.map fun i => x.getD i false).any id]) = _
    simp [List.any_map]
  have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ D := by decide
  have pos : RightOnIncidentPairs singerLines3 A := by
    intro l p hp
    rw [ev]
    simpa [P,incDef] using fit.1 p l ((geom p l).mp hp)
  have neg (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) :
      A.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
    have gq : good Q := by
      refine ⟨hq.1,fun l => ?_⟩
      have h : Q.filter (fun p => p-l ∈ D) = Q ∩ singerLines3 l := by ext p; simp [geom]
      rw [h]
      exact hq.2 l
    have nr : incidenceInput Q (missLines singerLines3 Q) = N Q := by
      change _ ++ _ = _ ++ _
      congr 1
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      simp [missDef,Finset.disjoint_right,geom]
    rw [ev,nr]
    exact fit.2 Q gq
  have h := core A hm hb pos neg (by
    intro b
    obtain ⟨r,v,pair⟩ := rows A pos neg b
    have h := packing _ b A hm r v pair
    by_contra! small
    have le := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_pred_of_lt small)
    cases b <;> simp at h le <;> omega)
  change 64 ≤ C.gates.length+1 at h
  exact Nat.le_of_succ_le_succ h

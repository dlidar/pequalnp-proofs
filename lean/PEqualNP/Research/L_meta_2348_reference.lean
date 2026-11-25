import PEqualNP.Research.L_meta_2348_star_extension
import PEqualNP.Research.L_meta_2348_absorption

set_option maxHeartbeats 1600000
namespace PEqualNP.Research.FanoReference
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Research.L_meta_2348_star_extension PEqualNP.Research.FlagAbsorption

local instance : DecidableEq GateOp := gateOpDecEq

def Fano (x : Fin 14 → Bool) : Prop :=
  ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (ptIdx u) ∧ x (lineIdx t)

def group (x : Fin 14 → Bool) (t : Fin 7) : Bool :=
  ((x (ptIdx t) || x (ptIdx (t+1))) || x (ptIdx (t+3))) && x (lineIdx t)

theorem group_spec (x : Fin 14 → Bool) : Fano x ↔ ∃ t, group x t = true := by
  unfold Fano group
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨u,t,h,hu,ht⟩
    refine ⟨t,?_,ht⟩
    rcases h with e | e | e <;> subst u <;> tauto
  · rintro ⟨t,h,ht⟩
    rcases h with (h|h)|h
    · exact ⟨t,t,Or.inl rfl,h,ht⟩
    · exact ⟨t+1,t,Or.inr (Or.inl rfl),h,ht⟩
    · exact ⟨t+3,t,Or.inr (Or.inr rfl),h,ht⟩

theorem stars_correct (x : Fin 14 → Bool) : stars.eval (List.ofFn x) = true ↔ Fano x := by
  rw [group_spec]
  let w := PEqualNP.Research.FanoTangent.scan PEqualNP.Research.FanoTangent.boolStep stars.gates (List.ofFn x)
  have raw (i : Fin 14) : w.getD i.val false = x i := by
    change (PEqualNP.Research.FanoTangent.scan PEqualNP.Research.FanoTangent.boolStep stars.gates _).getD _ _ = _
    rw [PEqualNP.Research.FanoTangent.scan_prefix _ _ _ _ _ (by simpa using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  have rule (j : ℕ) (hj : j < stars.size) :
      w.getD (14+j) false = (gateAt stars j).op.eval ((gateAt stars j).inputs.map (fun i => w.getD i false)) := by
    have rb := (show IsAO2 14 stars by decide).2.1 j hj
    have eqg : gateAt stars j = stars.gates[j] := List.getD_eq_getElem _ _ hj
    have e := PEqualNP.Research.FanoTangent.scan_gate PEqualNP.Research.FanoTangent.boolStep
      stars.gates (List.ofFn x) false j hj (by
        intro a b eq
        unfold PEqualNP.Research.FanoTangent.boolStep
        congr 1
        apply List.map_congr_left
        intro k hk
        apply eq
        rw [List.length_ofFn]
        apply rb k
        rwa [eqg])
    simpa only [List.length_ofFn,eqg,w,PEqualNP.Research.FanoTangent.boolStep] using e
  have w0 : w.getD 0 false = x 0 := raw 0
  have w1 : w.getD 1 false = x 1 := raw 1
  have w2 : w.getD 2 false = x 2 := raw 2
  have w3 : w.getD 3 false = x 3 := raw 3
  have w4 : w.getD 4 false = x 4 := raw 4
  have w5 : w.getD 5 false = x 5 := raw 5
  have w6 : w.getD 6 false = x 6 := raw 6
  have w7 : w.getD 7 false = x 7 := raw 7
  have w8 : w.getD 8 false = x 8 := raw 8
  have w9 : w.getD 9 false = x 9 := raw 9
  have w10 : w.getD 10 false = x 10 := raw 10
  have w11 : w.getD 11 false = x 11 := raw 11
  have w12 : w.getD 12 false = x 12 := raw 12
  have w13 : w.getD 13 false = x 13 := raw 13
  have w14 : w.getD 14 false = (x 0 || x 1) := by
    have e := rule 0 (by decide)
    change w.getD 14 false = GateOp.eval .or [w.getD 0 false, w.getD 1 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w0,w1] using e
  have w15 : w.getD 15 false = ((x 0 || x 1) || x 3) := by
    have e := rule 1 (by decide)
    change w.getD 15 false = GateOp.eval .or [w.getD 14 false, w.getD 3 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w14,w3] using e
  have w16 : w.getD 16 false = (((x 0 || x 1) || x 3) && x 7) := by
    have e := rule 2 (by decide)
    change w.getD 16 false = GateOp.eval .and [w.getD 15 false, w.getD 7 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w15,w7] using e
  have w17 : w.getD 17 false = (x 1 || x 2) := by
    have e := rule 3 (by decide)
    change w.getD 17 false = GateOp.eval .or [w.getD 1 false, w.getD 2 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w1,w2] using e
  have w18 : w.getD 18 false = ((x 1 || x 2) || x 4) := by
    have e := rule 4 (by decide)
    change w.getD 18 false = GateOp.eval .or [w.getD 17 false, w.getD 4 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w17,w4] using e
  have w19 : w.getD 19 false = (((x 1 || x 2) || x 4) && x 8) := by
    have e := rule 5 (by decide)
    change w.getD 19 false = GateOp.eval .and [w.getD 18 false, w.getD 8 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w18,w8] using e
  have w20 : w.getD 20 false = (x 2 || x 3) := by
    have e := rule 6 (by decide)
    change w.getD 20 false = GateOp.eval .or [w.getD 2 false, w.getD 3 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w2,w3] using e
  have w21 : w.getD 21 false = ((x 2 || x 3) || x 5) := by
    have e := rule 7 (by decide)
    change w.getD 21 false = GateOp.eval .or [w.getD 20 false, w.getD 5 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w20,w5] using e
  have w22 : w.getD 22 false = (((x 2 || x 3) || x 5) && x 9) := by
    have e := rule 8 (by decide)
    change w.getD 22 false = GateOp.eval .and [w.getD 21 false, w.getD 9 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w21,w9] using e
  have w23 : w.getD 23 false = (x 3 || x 4) := by
    have e := rule 9 (by decide)
    change w.getD 23 false = GateOp.eval .or [w.getD 3 false, w.getD 4 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w3,w4] using e
  have w24 : w.getD 24 false = ((x 3 || x 4) || x 6) := by
    have e := rule 10 (by decide)
    change w.getD 24 false = GateOp.eval .or [w.getD 23 false, w.getD 6 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w23,w6] using e
  have w25 : w.getD 25 false = (((x 3 || x 4) || x 6) && x 10) := by
    have e := rule 11 (by decide)
    change w.getD 25 false = GateOp.eval .and [w.getD 24 false, w.getD 10 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w24,w10] using e
  have w26 : w.getD 26 false = (x 4 || x 5) := by
    have e := rule 12 (by decide)
    change w.getD 26 false = GateOp.eval .or [w.getD 4 false, w.getD 5 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w4,w5] using e
  have w27 : w.getD 27 false = ((x 4 || x 5) || x 0) := by
    have e := rule 13 (by decide)
    change w.getD 27 false = GateOp.eval .or [w.getD 26 false, w.getD 0 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w26,w0] using e
  have w28 : w.getD 28 false = (((x 4 || x 5) || x 0) && x 11) := by
    have e := rule 14 (by decide)
    change w.getD 28 false = GateOp.eval .and [w.getD 27 false, w.getD 11 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w27,w11] using e
  have w29 : w.getD 29 false = (x 5 || x 6) := by
    have e := rule 15 (by decide)
    change w.getD 29 false = GateOp.eval .or [w.getD 5 false, w.getD 6 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w5,w6] using e
  have w30 : w.getD 30 false = ((x 5 || x 6) || x 1) := by
    have e := rule 16 (by decide)
    change w.getD 30 false = GateOp.eval .or [w.getD 29 false, w.getD 1 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w29,w1] using e
  have w31 : w.getD 31 false = (((x 5 || x 6) || x 1) && x 12) := by
    have e := rule 17 (by decide)
    change w.getD 31 false = GateOp.eval .and [w.getD 30 false, w.getD 12 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w30,w12] using e
  have w32 : w.getD 32 false = (x 6 || x 0) := by
    have e := rule 18 (by decide)
    change w.getD 32 false = GateOp.eval .or [w.getD 6 false, w.getD 0 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w6,w0] using e
  have w33 : w.getD 33 false = ((x 6 || x 0) || x 2) := by
    have e := rule 19 (by decide)
    change w.getD 33 false = GateOp.eval .or [w.getD 32 false, w.getD 2 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w32,w2] using e
  have w34 : w.getD 34 false = (((x 6 || x 0) || x 2) && x 13) := by
    have e := rule 20 (by decide)
    change w.getD 34 false = GateOp.eval .and [w.getD 33 false, w.getD 13 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w33,w13] using e
  have w35 : w.getD 35 false = ((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) := by
    have e := rule 21 (by decide)
    change w.getD 35 false = GateOp.eval .or [w.getD 16 false, w.getD 19 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w16,w19] using e
  have w36 : w.getD 36 false = (((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) := by
    have e := rule 22 (by decide)
    change w.getD 36 false = GateOp.eval .or [w.getD 35 false, w.getD 22 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w35,w22] using e
  have w37 : w.getD 37 false = ((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) := by
    have e := rule 23 (by decide)
    change w.getD 37 false = GateOp.eval .or [w.getD 36 false, w.getD 25 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w36,w25] using e
  have w38 : w.getD 38 false = (((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) || (((x 4 || x 5) || x 0) && x 11)) := by
    have e := rule 24 (by decide)
    change w.getD 38 false = GateOp.eval .or [w.getD 37 false, w.getD 28 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w37,w28] using e
  have w39 : w.getD 39 false = ((((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) || (((x 4 || x 5) || x 0) && x 11)) || (((x 5 || x 6) || x 1) && x 12)) := by
    have e := rule 25 (by decide)
    change w.getD 39 false = GateOp.eval .or [w.getD 38 false, w.getD 31 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w38,w31] using e
  have w40 : w.getD 40 false = (((((((((x 0 || x 1) || x 3) && x 7) || (((x 1 || x 2) || x 4) && x 8)) || (((x 2 || x 3) || x 5) && x 9)) || (((x 3 || x 4) || x 6) && x 10)) || (((x 4 || x 5) || x 0) && x 11)) || (((x 5 || x 6) || x 1) && x 12)) || (((x 6 || x 0) || x 2) && x 13)) := by
    have e := rule 26 (by decide)
    change w.getD 40 false = GateOp.eval .or [w.getD 39 false, w.getD 34 false] at e
    simpa only [GateOp.eval, List.all_cons,List.all_nil,List.any_cons,List.any_nil, Bool.and_true,Bool.or_false,id_eq, w39,w34] using e
  change w.getD 40 false = true ↔ _
  rw [w40]
  change (((((((group x 0 || group x 1) || group x 2) || group x 3) || group x 4) || group x 5) || group x 6)) = true ↔ _
  simp only [Bool.or_eq_true]
  constructor
  · intro h
    rcases h with ((((((h|h)|h)|h)|h)|h)|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
    · exact ⟨5,h⟩
    · exact ⟨6,h⟩
  · rintro ⟨t,h⟩
    fin_cases t
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

def ref29 := extend 14 stars 16

theorem size_ref : ref29.size = 29 := by decide
theorem reference_correct (x : Fin 14 → Bool) : ref29.eval (List.ofFn x) = true ↔ Fano x := by
  rw [ref29,unchanged 14 stars 16 (by decide) _ (by simp)]
  exact stars_correct x

theorem reference_AO : IsAO2 14 ref29 := by decide +kernel
theorem reference_distinct : ∀ j < ref29.size, opnd ref29 j 0 ≠ opnd ref29 j 1 := by decide +kernel
theorem reference_first : (gateAt ref29 0).op = .or := rfl

/-- The two old operands of the final OR have vanishing constant term on every flag
in either orientation, including when the chosen point or line is outside star zero. -/
theorem old_constants : ∀ (s : Bool) (u t : Fin 7),
    let x := (List.range 14).map fun i => i == (ptIdx u).val || i == (lineIdx t).val
    let w := PEqualNP.ReadK.linearParts stars (fun i => i == (if s then (lineIdx t).val else (ptIdx u).val)) x
    (w.getD stars.output (false,false)).1 = false ∧ (w.getD 16 (false,false)).1 = false := by
  decide +kernel

theorem reference_all_flags (s : Bool) (u t : Fin 7) :
    PEqualNP.ReadK.lineSingle ref29 14 (fun i => i == (if s then (lineIdx t).val else (ptIdx u).val))
      (ptIdx u).val (lineIdx t).val = false := by
  have h := old_constants s u t
  exact congrArg Prod.snd (kills_linear 14 stars 16 (by decide) _ _ (by simp) h.1 h.2)

/-- The exact posted assertion fails when its gate budget is increased from 27 to 29. -/
theorem refutes_29 : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (29 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False) := by
  intro h
  apply h ref29 (by decide) reference_AO reference_distinct reference_first
  · exact reference_correct
  · intro s
    cases s
    · refine ⟨fun w => (4376706007041 : ℕ).testBit w, ?_, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
      · decide +kernel
    · refine ⟨fun w => (4363686838400 : ℕ).testBit w, ?_, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
      · decide +kernel

#print axioms stars_correct
#print axioms reference_correct
#print axioms reference_all_flags
#print axioms refutes_29
end PEqualNP.Research.FanoReference

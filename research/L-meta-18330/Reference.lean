import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

private def candidate : Circuit :=
  ⟨[⟨.or,[7,11]⟩,
    ⟨.or,[14,13]⟩,
    ⟨.and,[0,15]⟩,
    ⟨.or,[7,8]⟩,
    ⟨.or,[17,12]⟩,
    ⟨.and,[1,18]⟩,
    ⟨.or,[8,9]⟩,
    ⟨.or,[20,13]⟩,
    ⟨.and,[2,21]⟩,
    ⟨.or,[7,9]⟩,
    ⟨.or,[23,10]⟩,
    ⟨.and,[3,24]⟩,
    ⟨.or,[8,10]⟩,
    ⟨.or,[26,11]⟩,
    ⟨.and,[4,27]⟩,
    ⟨.or,[9,11]⟩,
    ⟨.or,[29,12]⟩,
    ⟨.and,[5,30]⟩,
    ⟨.or,[10,12]⟩,
    ⟨.or,[32,13]⟩,
    ⟨.and,[6,33]⟩,
    ⟨.or,[16,19]⟩,
    ⟨.or,[35,22]⟩,
    ⟨.or,[36,25]⟩,
    ⟨.or,[37,28]⟩,
    ⟨.or,[38,31]⟩,
    ⟨.or,[39,34]⟩], 40⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 900000 in
theorem PEqualNP.Research.Fano.reference27 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧ ∀ (x2 : Fin (7 : ℕ) → Bool), x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬(x5 = x4 ∨ x5 = x4 + (1 : Fin (7 : ℕ)) ∨ x5 = x4 + (3 : Fin (7 : ℕ))))) x3) = Bool.false := by
  refine ⟨candidate,by decide,?_,?_,?_⟩
  · have allOk : ∀ j : Fin candidate.gates.length,
        let g := candidate.gates[j.val]
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j.val ∧ b < 14+j.val := by
      change ∀ j : Fin 27, _
      intro j
      fin_cases j <;> first | (left; rfl) | (refine ⟨Or.inl rfl,_,_,rfl,by decide,by decide,by decide⟩) | (refine ⟨Or.inr rfl,_,_,rfl,by decide,by decide,by decide⟩)
    intro j g hj
    have hlt : j < candidate.gates.length := List.getElem?_eq_some_iff.mp hj |>.1
    have eq : candidate.gates[j] = g := by simpa [hlt] using hj
    subst g
    exact allOk ⟨j,hlt⟩
  · decide +kernel
  · decide +kernel

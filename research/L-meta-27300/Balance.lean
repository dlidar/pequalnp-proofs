import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds
theorem balance_aux (ws : ℕ → ℕ) (m : ℕ) (gs : List Gate)
    (hg : ∀ j : Fin gs.length, ws (m+j.val) ≤ (((gs.get j).inputs.map ws).sum)) :
    ((List.range (m+gs.length)).map ws).sum ≤ ((List.range m).map ws).sum +
      ((gs.flatMap Gate.inputs).map ws).sum := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    have h0 := hg ⟨0,by simp⟩
    have hfirst : ws m ≤ (g.inputs.map ws).sum := by simpa using h0
    have htail : ∀ j : Fin gs.length, ws (m+1+j.val) ≤ (((gs.get j).inputs.map ws).sum) := by
      intro j
      have h := hg ⟨j.val+1,by simp <;> omega⟩
      simpa [Nat.add_assoc,Nat.add_comm 1 j.val,List.get_eq_getElem] using h
    have t := ih (m+1) htail
    rw [List.range_succ, List.map_append,List.sum_append] at t
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at t
    simp only [List.length_cons,List.flatMap_cons,List.map_append,List.sum_append]
    rw [show m+(gs.length+1) = m+1+gs.length by omega]
    omega

theorem output_budget (ws : ℕ → ℕ) (m : ℕ) (gs : List Gate) (o : ℕ)
    (h : (List.range (m+gs.length)).Perm (o::gs.flatMap Gate.inputs))
    (hg : ∀ j : Fin gs.length, ws (m+j.val) ≤ (((gs.get j).inputs.map ws).sum)) :
    ws o ≤ ((List.range m).map ws).sum := by
  have eq := (h.map ws).sum_eq
  have le := balance_aux ws m gs hg
  simp only [List.map_cons,List.sum_cons] at eq
  omega
end PEqualNP.Research.Permanent27300

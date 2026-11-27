import Density
import Amplify

namespace PEqualNP.Research.PlaneConsequence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.ReadK PEqualNP.Research.ReadTwoDensity PEqualNP.Research.ReadAmplification

theorem eval_incidence {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) :
    (amplify (N+N) C).eval (incidenceInput X Y) = C.eval (incidenceInput X Y) := by
  let v := incidenceInput X Y
  have hl : v.length = N+N := by simp [v,incidenceInput]
  let z : Fin (N+N) → Bool := fun i => v.getD i.val false
  have e : List.ofFn z = v := by
    apply List.ext_getElem
    · simpa using hl.symm
    · intro i h1 h2
      simp only [List.getElem_ofFn]; exact List.getD_eq_getElem _ _ h2
  have h := amplifyValue C z
  change (amplify (N+N) C).eval (List.ofFn z) = C.eval (List.ofFn z) at h
  simpa only [e] using h

theorem allFlagsHard {N q : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 1 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output < N+N+C.size)
    (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    {p l : Fin N} (hp : p ∈ S l) :
    readsAtMost (amplify (N+N) C) (N+N) (setList {Fin.castAdd N p,Fin.natAdd N l}) 2 = false :=
  amplifyHard h ho (flagPrime hq h hr hf hp) (by simp)

def Posted : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 → x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size

/-- The posted result would bound all proper-output circuits on the same tests up to three gates. -/
theorem transfer (posted : Posted) (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output < N+N+C.size)
    (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    N*q ≤ 100*(C.size+3) := by
  let D := amplify (N+N) C
  obtain ⟨hD,hlo,hhi,hor⟩ := amplifyModel h ho
  have right : RightOnIncidentPairs S D := by
    intro l p hp
    rw [show D = _ from rfl,eval_incidence]
    exact hr l p hp
  have reject (X Y : Finset (Fin N)) (hy : Y.card ≤ q) (hxy : IsFalseInput S X Y) :
      D.eval (incidenceInput X Y) = false := by
    rw [show D = _ from rfl,eval_incidence]
    exact hf X Y hy hxy
  let l : Fin N := ⟨0,by omega⟩
  obtain ⟨p,hp⟩ : (S l).Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
  have fails : ¬ IsReadK (N+N) D 2 := by
    intro hk
    have yes := hk _ (flagPrime (by omega : 1 ≤ q) hD right reject hp)
    have no := allFlagsHard (by omega : 1 ≤ q) h ho hr hf hp
    rw [no] at yes
    contradiction
  simpa only [D,amplifySize] using posted q N S D hq hN hc hu hD fails hlo hhi hor right reject

end PEqualNP.Research.PlaneConsequence

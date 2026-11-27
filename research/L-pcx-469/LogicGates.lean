import Threshold
namespace SpinCircuit
open Finset
variable {X : Type} {n : ℕ} (E : Encoding X n)
noncomputable def gateP (U r : ℕ) (P : X → Prop) : Prop := by
  classical exact level E U r (fun x => decide (P x))

theorem of_bool {U r : ℕ} {P : X → Prop} {f : X → Bool} (h : level E U r f) (he : ∀ x, f x = true ↔ P x) : gateP E U r P := by
  classical
  unfold gateP
  convert h using 1
  funext x;apply Bool.eq_iff_iff.mpr;simpa using (he x).symm

theorem to_bool {U r : ℕ} {P : X → Prop} {f : X → Bool} (h : gateP E U r P) (he : ∀ x, f x = true ↔ P x) : level E U r f := by
  classical
  unfold gateP at h
  convert h using 1
  funext x;apply Bool.eq_iff_iff.mpr;simpa using he x

theorem gate_const (U r : ℕ) (P : Prop) : gateP E U r (fun _ => P) := by
  classical
  exact level_const E U r (decide P)

theorem gate_not {U r : ℕ} (hU : 4 ≤ U) {P : X → Prop} (h : gateP E U r P) :
    gateP E U (r+1) (fun x => ¬P x) := by
  classical
  simpa only [gateP,decide_not] using level_not E hU h

theorem gate_lift {U r v : ℕ} (hU : 1 ≤ U) (hr : r≤v) {P : X→Prop} (hf : gateP E U r P) :
    gateP E U v P := lift_level E hU hr hf

theorem gate_congr {U r : ℕ} {P Q : X→Prop} (h : gateP E U r P) (eqv : ∀ x, P x ↔ Q x) :
    gateP E U r Q := by have := funext (fun x => propext (eqv x)); rwa [← this]

theorem gate_card {J : Type} [Fintype J] {U r : ℕ} (hU : 4 ≤ U) (hl : Fintype.card J ≤ U)
    (P : J → X → Prop) [∀ j, DecidablePred (P j)] [∀ x, DecidablePred (fun i => P i x)]
    (h : ∀ j, gateP E U r (P j)) (a : ℕ) :
    gateP E U (r+4) (fun x => a ≤ (univ.filter (fun j => P j x)).card) := by
  classical
  let e := Fintype.equivFin J
  let fs := fun (i : Fin (Fintype.card J)) (x : X) => decide (P (e.symm i) x)
  have hf (i) : level E U r (fs i) := to_bool E (h (e.symm i)) (by intro x;simp [fs])
  have ht := level_threshold E hU hl fs hf a
  have eqv (x : X) : onCount fs x = (univ.filter (fun j => P j x)).card := by
    unfold onCount
    rw [e.symm.sum_comp (fun j => (decide (P j x)).toNat)] <;> try rfl
    have hz (j : J) : (decide (P j x)).toNat = if P j x then 1 else 0 := by by_cases hj : P j x <;> simp [hj]
    simp_rw [hz]
    exact sum_boole _ _
  apply of_bool E ht
  intro x; simp [eqv]

theorem gate_all {J : Type} [Fintype J] {U r : ℕ} (hU : 4 ≤ U) (hl : Fintype.card J ≤ U)
    (P : J → X → Prop) (h : ∀ j, gateP E U r (P j)) :
    gateP E U (r+4) (fun x => ∀ j, P j x) := by
  classical
  apply gate_congr E (gate_card E hU hl P h (Fintype.card J))
  intro x
  have hcap := card_filter_le univ (fun j => P j x)
  rw [card_univ] at hcap
  rw [show Fintype.card J = (univ : Finset J).card from rfl]
  rw [le_iff_eq_or_lt,eq_comm,card_filter_eq_iff]
  simp_all

theorem gate_and {U r : ℕ} (hU : 4 ≤ U) {P Q : X → Prop} (hP : gateP E U r P) (hQ : gateP E U r Q) :
    gateP E U (r+4) (fun x => P x ∧ Q x) := by
  let R := fun (b : Bool) => if b then P else Q
  have hr (b) : gateP E U r (R b) := by cases b <;> assumption
  apply gate_congr E (gate_all E hU (by simpa using (show 2≤U by omega)) R hr)
  intro x; simp [R,and_comm]

end SpinCircuit

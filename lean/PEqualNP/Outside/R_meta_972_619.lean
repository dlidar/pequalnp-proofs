import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pinning an input deletes each gate that reads it. If both endpoints of a flag
-- have four readers, they must share a gate or deleting both removes eight.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_619
    (pin_readers : ∀ (n : ℕ) (S : Finset (Fin n)) (C : Circuit), Monotone2 C →
      let pin := fun (x : Fin n → Bool) i => if i ∈ S then false else x i
      let count := C.gates.countP (fun g => g.inputs.any fun k => decide (∃ i ∈ S, (i : ℕ) = k))
      (∃ x, C.eval (List.ofFn (pin x)) = false) →
      ∃ R : Circuit, Monotone2 R ∧ R.size + count ≤ C.size ∧
        ∀ x, R.eval (List.ofFn x) = C.eval (List.ofFn (pin x)))
    (one : let near := fun (u v : Fin 26) => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ)
      ∀ k : Fin 26,
      let S : Finset (Fin 26) := {k}
      ∀ R : Circuit, Monotone2 R → (∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 26, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true) → 59 ≤ R.size)
    (pair : let near := fun (u v : Fin 26) => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ)
      ∀ i j : Fin 26, near i j →
      let S : Finset (Fin 26) := {i,j}
      ∀ R : Circuit, Monotone2 R → (∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 26, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true) → 56 ≤ R.size)
    (core : let near := fun (u v : Fin 26) => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ)
      ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, near u v ∧ x u = true ∧ x v = true) →
      let readers := fun (i : Fin 26) => C.gates.countP (fun g => decide (i.val ∈ g.inputs))
      (∀ i, readers i ≤ 4) →
      (∀ i j, near i j → readers i = 4 → readers j = 4 →
        ∃ g ∈ C.gates, i.val ∈ g.inputs ∧ j.val ∈ g.inputs) → 64 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C hm ok
  by_contra! short
  let near := fun (u v : Fin 26) => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ)
  have encode : ∀ u v : Fin 26, (u.val,v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔ near u v := by decide +kernel
  have computes (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, near u v ∧ x u = true ∧ x v = true := by
    simpa only [encode] using ok x
  let cost := fun (S : Finset (Fin 26)) =>
    C.gates.countP (fun g => g.inputs.any fun k => decide (∃ i ∈ S, (i : ℕ) = k))
  have delete (S : Finset (Fin 26)) : ∃ R : Circuit, Monotone2 R ∧ R.size + cost S ≤ C.size ∧
      ∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true := by
    let pin := fun (x : Fin 26 → Bool) (i : Fin 26) => if i ∈ S then false else x i
    have zero : C.eval (List.ofFn (pin (fun _ => false))) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨u,v,_,hit,_⟩ := (computes _).mp h
      simp [pin] at hit
    obtain ⟨R,m,b,eq⟩ := pin_readers 26 S C hm ⟨_,zero⟩
    refine ⟨R,m,b,?_⟩
    intro x
    rw [eq,computes]
    constructor
    · rintro ⟨u,v,e,hu,hv⟩
      by_cases a : u ∈ S
      · simp [a] at hu
      by_cases b : v ∈ S
      · simp [b] at hv
      exact ⟨u,v,e,a,b,by simpa [a] using hu,by simpa [b] using hv⟩
    · rintro ⟨u,v,e,a,b,hu,hv⟩
      exact ⟨u,v,e,by simpa [a] using hu,by simpa [b] using hv⟩
  let readers := fun (i : Fin 26) => C.gates.countP (fun g => decide (i.val ∈ g.inputs))
  have single (i : Fin 26) : cost {i} = readers i := by
    apply List.countP_congr
    intro g _
    simp
  have few (i : Fin 26) : readers i ≤ 4 := by
    obtain ⟨R,m,b,okR⟩ := delete {i}
    have lb := one i R m okR
    rw [single] at b
    omega
  apply (Nat.not_le_of_gt short) (core C hm computes few ?_)
  intro i j adjacent hi hj
  obtain ⟨R,m,b,okR⟩ := delete {i,j}
  have lb := pair i j adjacent R m okR
  by_contra! none
  have split (gs : List Gate) (inC : ∀ g ∈ gs, g ∈ C.gates) :
      gs.countP (fun g => g.inputs.any fun k => decide (∃ a ∈ ({i,j} : Finset (Fin 26)), a.val = k)) =
      gs.countP (fun g => decide (i.val ∈ g.inputs)) + gs.countP (fun g => decide (j.val ∈ g.inputs)) := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have ihcounts := ih (fun z hz => inC z (List.mem_cons_of_mem _ hz))
      have h₀ := none g (inC g List.mem_cons_self)
      have test : (g.inputs.any fun k => decide (∃ a ∈ ({i,j} : Finset (Fin 26)), a.val = k)) =
          (decide (i.val ∈ g.inputs) || decide (j.val ∈ g.inputs)) := by
        apply Bool.eq_iff_iff.mpr
        simp [exists_or,or_and_right]
        grind
      rw [List.countP_cons,List.countP_cons,List.countP_cons,test,ihcounts]
      by_cases gi : i.val ∈ g.inputs <;> by_cases gj : j.val ∈ g.inputs <;> simp_all <;> omega
  have number : cost {i,j} = readers i + readers j := split C.gates (fun _ h => h)
  change readers i = 4 at hi
  change readers j = 4 at hj
  omega

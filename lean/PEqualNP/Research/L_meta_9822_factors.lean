import PEqualNP.Research.L_meta_9822_profiles

namespace PEqualNP.Research.PuncturedPetersen
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Every exact factor independent of the specified positions is forced true
where the target accepts a completion in those positions. -/
def IndependentOf (u : Nat → Bool) (m : Nat) := ∀ x, u (x ||| m) = u x
def majorant (u : Nat → Bool) := ∀ x, target x = true → u x = true

theorem forced (u : Nat → Bool) (m : Nat) (hu : IndependentOf u m) (above : majorant u)
    (x : Nat) (h : target (x ||| m) = true) : u x = true := hu x ▸ above _ h

theorem attained (m : Nat) : IndependentOf (fun x => target (x ||| m)) m ∧
    majorant (fun x => target (x ||| m)) := ⟨by intro x; simp [Nat.or_assoc],fun _ h => extend h m⟩

/-- If the omitted positions contain an edge, this factor is the constant true. -/
theorem full_if_edge (u : Nat → Bool) (m : Nat) (hu : IndependentOf u m)
    (above : majorant u) (edge : target m = true) : ∀ x, u x = true := by
  intro x
  exact forced u m hu above x (by simpa [Nat.or_comm] using extend edge x)

def pop (x : Nat) := ((List.range 10).filter x.testBit).length
theorem independence_number : (∀ m : Fin 1024, target m.val = false → pop m.val ≤ 4) ∧
    ((List.range 1024).filter (fun m => ! target m && decide (pop m=4))).length = 13 := by decide +kernel

theorem factor_support (u : Nat → Bool) (m : Fin 1024) (hu : IndependentOf u m)
    (above : majorant u) (nontrivial : ∃ x, u x = false) : pop m.val ≤ 4 := by
  apply independence_number.1
  cases eq : target m.val with
  | false => rfl
  | true =>
    obtain ⟨x,h⟩ := nontrivial
    rw [full_if_edge u m hu above eq x] at h
    contradiction

def conjunction (omitted : List Nat) (x : Nat) :=
  omitted.all (fun i => target (x ||| 2^i))
def works (omitted : List Nat) := (List.range 1024).all fun x => conjunction omitted x == target x
def fromMask (m : Nat) := (List.range 10).filter m.testBit
def triples : List Nat := [25,49,70,134,280]

theorem threshold : ∀ m : Fin 1024, pop m.val ≤ 3 → works (fromMask m.val) = triples.contains m.val := by decide +kernel

/-- Completeness of the cofactor test for arbitrary Boolean factors, including nonmonotone ones. -/
theorem exact_test (I : List Nat) (inRange : ∀ i ∈ I, i < 10) :
    works I = true ↔ ∃ F : Nat → Nat → Bool, (∀ i ∈ I, IndependentOf (F i) (2^i)) ∧
      ∀ x < 1024, (I.all fun i => F i x) = target x := by
  constructor
  · intro h
    refine ⟨fun i x => target (x ||| 2^i),fun i _ => (attained _).1,?_⟩
    intro x hx
    exact beq_iff_eq.mp (List.all_eq_true.mp h x (List.mem_range.mpr hx))
  · rintro ⟨F,localF,agrees⟩
    apply List.all_eq_true.mpr
    intro x hx
    have bound := List.mem_range.mp hx
    apply beq_iff_eq.mpr
    cases h : target x with
    | true =>
      exact List.all_eq_true.mpr (fun i _ => extend h (2^i))
    | false =>
      cases ht : conjunction I x with
      | false => rfl
      | true =>
        have on : (I.all fun i => F i x) = true := by
          apply List.all_eq_true.mpr
          intro i hi
          let y := x ||| 2^i
          have ok : target y = true := List.all_eq_true.mp ht i hi
          have small : y < 1024 := Nat.or_lt_two_pow bound (Nat.pow_lt_pow_right (by decide : 1<2) (by simpa using inRange i hi))
          have allY := (agrees y small).trans ok
          exact (localF i hi x) ▸ (List.all_eq_true.mp allY i hi)
        rw [agrees x bound,h] at on
        contradiction
end PEqualNP.Research.PuncturedPetersen

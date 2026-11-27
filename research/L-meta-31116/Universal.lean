import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic

namespace InverterRepair

variable {α : Type*} [Preorder α]

def Decoder (D : α → Bool → Bool) : Prop :=
  (∀ b, Monotone (fun x => D x b)) ∧ ∀ x, Monotone (D x)

def Universal (f h u : α → Bool) : Prop :=
  ∀ D : α → Bool → Bool, Decoder D → (∀ x, D x (!(h x)) = f x) →
    ∀ x, D x (u x) = f x

def muxTest (a b z : Bool) : Bool := (a && b) || (z && (a || b))

@[local simp] theorem leFalse (x : Bool) : x ≤ false ↔ x = false := by cases x <;> decide
@[local simp] theorem trueLe (x : Bool) : true ≤ x ↔ x = true := by cases x <;> decide

theorem mux_monotone {a b z a' b' z' : Bool} (ha : a ≤ a') (hb : b ≤ b') (hz : z ≤ z') :
    muxTest a b z ≤ muxTest a' b' z' := by
  revert ha hb hz; decide +revert

theorem universal_iff (f h u : α → Bool) (hf : Monotone f) (hh : Monotone h) :
    Universal f h u ↔ ∀ x, f x ≠ h x → u x = f x := by
  constructor
  · intro ok
    let D := fun x z => muxTest (f x) (h x) z
    have hd : Decoder D := ⟨fun _ _ _ hxy => mux_monotone (hf hxy) (hh hxy) le_rfl,
      fun _ _ _ hz => mux_monotone le_rfl le_rfl hz⟩
    have orig : ∀ x, D x (!(h x)) = f x := by
      intro x; dsimp [D]; cases f x <;> cases h x <;> rfl
    intro x diff
    have y := ok D hd orig x
    dsimp [D] at y
    cases a : f x <;> cases b : h x <;> cases c : u x <;> simp_all [muxTest]
  · intro matchOn D hd orig x
    have exactAt := orig x
    by_cases same : f x = h x
    · cases a : f x <;> have b := same.symm.trans a
      · have hh' := hd.2 x (Bool.le_true (u x))
        simp [b,a] at exactAt
        simpa [a,exactAt] using hh'
      · have hh' := hd.2 x (Bool.false_le (u x))
        simp [b,a] at exactAt
        simpa [a,exactAt] using hh'
    · have val := matchOn x same
      have flip : u x = !(h x) := by
        cases a : f x <;> cases b : h x <;> simp_all
      simpa [flip] using exactAt

theorem boundary_iff (f h u : α → Bool) (hf : Monotone f) (hh : Monotone h) (hu : Monotone u)
    (P N : α → Prop) (hp : ∀ p, P p → f p = true) (hn : ∀ n, N n → f n = false)
    (pc : ∀ x, f x = true → ∃ p, P p ∧ p ≤ x)
    (nc : ∀ x, f x = false → ∃ n, N n ∧ x ≤ n) :
    Universal f h u ↔ (∀ p, P p → h p = false → u p = true) ∧
      (∀ n, N n → h n = true → u n = false) := by
  rw [universal_iff f h u hf hh]
  constructor
  · intro exactOn
    constructor
    · intro p mem off; have val := hp p mem
      exact (exactOn p (by simp [val,off])).trans val
    · intro n mem on; have val := hn n mem
      exact (exactOn n (by simp [val,on])).trans val
  · rintro ⟨yes,no⟩ x diff
    cases e : f x
    · obtain ⟨n,mem,le⟩ := nc x e
      have on : h x = true := by cases eq : h x <;> simp_all
      have nn : h n = true := by simpa [on] using hh le
      simpa [no n mem nn] using hu le
    · obtain ⟨p,mem,le⟩ := pc x e
      have off : h x = false := by cases eq : h x <;> simp_all
      have pp : h p = false := by simpa [off] using hh le
      simpa [yes p mem pp] using hu le

-- A previously computed copy of the inverter input cannot improve the best monotone repair.
theorem discard_original (f h : α → Bool) (hf : Monotone f) (hh : Monotone h)
    (R : α → Bool → Bool) (hr : ∀ x, Monotone (R x))
    (good : Universal f h (fun x => R x (h x))) (s : α → Bool) :
    Universal f h (fun x => R x (s x)) := by
  rw [universal_iff f h _ hf hh] at good ⊢
  intro x diff
  have a := good x diff
  cases e : f x
  · have b : h x=true := by cases t : h x <;> simp_all
    have c := hr x (Bool.le_true (s x))
    simp [b,e] at a
    simpa [a] using c
  · have b : h x=false := by cases t : h x <;> simp_all
    have c := hr x (Bool.false_le (s x))
    simp [b,e] at a
    simpa [a] using c
end InverterRepair

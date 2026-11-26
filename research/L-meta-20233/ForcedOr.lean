import Mathlib

namespace PairEncoding20233
abbrev Label := Fin 8
structure Input where
  row : Label
  col : Label
  deriving DecidableEq, Fintype
def edge (i j : Label) : Bool := (14466700110149527140 : Nat).testBit (8*i.val+j.val)
def bits (i j : Label) (x : Input) : Bool × Bool := (decide (x.row=i),decide (x.col=j))
def restLE (i j : Label) (x y : Input) : Prop :=
  (x.row=i ∨ x.row=y.row) ∧ (x.col=j ∨ x.col=y.col)
instance (i j : Label) (x y : Input) : Decidable (restLE i j x y) := by unfold restLE; infer_instance
def Need (i j : Label) (s t : Bool × Bool) : Prop :=
  ∃ x y : Input, edge x.row x.col = true ∧ edge y.row y.col = false ∧
    restLE i j x y ∧ bits i j x = s ∧ bits i j y = t
instance (i j : Label) (s t : Bool × Bool) : Decidable (Need i j s t) := by unfold Need; infer_instance
-- For a nonedge, either single-coordinate state must distinguish a positive from an
-- outside-larger negative having neither coordinate.
def Admits (i j : Label) (f : Bool × Bool → Bool) : Prop :=
  ∀ x y : Input, restLE i j x y → f (bits i j x) ≤ f (bits i j y) → edge x.row x.col ≤ edge y.row y.col
theorem forces {i j : Label} {f : Bool × Bool → Bool} (h : Admits i j f)
    {s t : Bool × Bool} (hn : Need i j s t) : f s = true ∧ f t = false := by
  rcases hn with ⟨x,y,hx,hy,le,hs,ht⟩
  have n : ¬ f s ≤ f t := by
    intro hh
    rw [← hs,← ht] at hh
    have out := h x y le hh
    rw [hx,hy] at out
    exact (by decide : ¬ true ≤ false) out
  cases fs : f s <;> cases ft : f t <;> simp_all
theorem rows_forced : ∀ i j : Label, edge i j = false →
    (Need i j (true,false) (false,false) ∧ Need i j (false,true) (false,false)) := by
  decide +kernel
theorem only_or {i j : Label} (off : edge i j = false) {f : Bool × Bool → Bool}
    (mon : Monotone f) (fit : Admits i j f) : ∀ s, f s = (s.1 || s.2) := by
  obtain ⟨h₁,h₂⟩ := rows_forced i j off
  obtain ⟨u,z⟩ := forces fit h₁
  have v := (forces fit h₂).1
  have w := mon (show (true,false) ≤ (true,true) by decide)
  rw [u] at w
  have both : f (true,true) = true := by
    cases hb : f (true,true) with
    | false => rw [hb] at w; exact False.elim ((by decide : ¬ true ≤ false) w)
    | true => rfl
  rintro ⟨a,b⟩
  cases a <;> cases b <;> simp_all

end PairEncoding20233
#print axioms PairEncoding20233.rows_forced
#print axioms PairEncoding20233.only_or

import Mathlib.Tactic
namespace PEqualNP.Research.PuncturedPlane9838
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

def available (R : Finset B) (N : A → Finset B) (x : Finset A) : Finset B :=
  R.filter fun b => ∀ a ∈ x, b ∉ N a

/-- Point and line masks form an independent assignment precisely when
no activated line is a neighbor of an activated point. -/
def independentPairs (L : Finset A) (R : Finset B) (N : A → Finset B) :=
  {p : Finset A × Finset B // p.1 ⊆ L ∧ p.2 ⊆ R ∧ ∀ a ∈ p.1, Disjoint (N a) p.2}

omit [DecidableEq A] in
theorem subset_available (R : Finset B) (N : A → Finset B) (x : Finset A) (y : Finset B) :
    y ⊆ available R N x ↔ y ⊆ R ∧ ∀ a ∈ x, Disjoint (N a) y := by
  simp only [Finset.subset_iff, available, Finset.mem_filter, Finset.disjoint_left]
  grind

def pairChoices (L : Finset A) (R : Finset B) (N : A → Finset B) :
    independentPairs L R N ≃ ((x : ↑L.powerset) × ↑(available R N x.val).powerset) where
  toFun s := ⟨⟨s.val.1, Finset.mem_powerset.mpr s.2.1⟩,
    ⟨s.val.2, Finset.mem_powerset.mpr ((subset_available ..).mpr s.2.2)⟩⟩
  invFun x := ⟨(x.1.val,x.2.val), Finset.mem_powerset.mp x.1.2,
    (subset_available ..).mp (Finset.mem_powerset.mp x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq A] in
theorem count_independent_pairs (L : Finset A) (R : Finset B) (N : A → Finset B) :
    Nat.card (independentPairs L R N) =
      ∑ x : ↑L.powerset, 2 ^ (available R N x.val).card := by
  classical
  rw [Nat.card_congr (pairChoices L R N), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp
end PEqualNP.Research.PuncturedPlane9838

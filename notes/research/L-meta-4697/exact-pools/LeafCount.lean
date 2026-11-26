import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import PEqualNP.Defs.TwoColour
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-!
# Partial results for L-meta-4675

For a disjunction of sound rectangles, shared OR preprocessing still costs
enough to obtain the edge-plus-cover lower bound. For nested monotone operands
whose conjunction implies the target, their off-target pair sets must satisfy
a crossing condition. An off-target rectangle on one side confines all
opposite off-target pairs to one row and one column. More generally one
operand has a cover of at most four vertices for its off-target pairs.
Two operands cannot both have five disjoint off-target pairs: two-colouring
the 5 by 5 crossing grid would force a target four-cycle. An explicit
pair of graph operands needs all four covering vertices on each side.
The gate-count argument for unrestricted nesting remains open.

The full circuit evaluator is used in the endpoint bound, the monotone-wire
result, and the matching example. The project also treats pair-clean circuits
in the auxiliary cleanBound theorem in L_meta_1892.
-/

namespace PEqualNP.Research.StarNetworks

open Finset

-- A wire denotes a set of leaves. Raw wires have at most one leaf.
-- Expanding several output wires backwards counts a shared union gate once.
theorem leaves_le {V : Type*} [DecidableEq V] (n s : ℕ) (W : ℕ → Finset V)
    (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (T : Finset V) (F : Finset ℕ)
    (valid : ∀ i ∈ F, i < n+s) (inside : ∀ i ∈ F, W i ⊆ T) :
    (F.biUnion W).card ≤ F.card +
      ((range s).filter fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ T).card := by
  classical
  induction s generalizing F with
  | zero =>
    have bound := card_biUnion_le (s := F) (t := W)
    have h := sum_le_sum (s := F) (g := fun _ => 1) (fun i hi => raw i (by simpa using valid i hi))
    simpa using bound.trans h
  | succ s ih =>
    let k := n+s
    let good := fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ T
    let c := ((range s).filter good).card
    have count : ((range (s+1)).filter good).card = c + (if good s then 1 else 0) := by
      rw [range_add_one,filter_insert]
      split <;> simp_all [c]
    change _ ≤ F.card + ((range (s+1)).filter good).card
    rw [count]
    have prev := ih (fun j hj => gate j (by omega))
    by_cases hit : k ∈ F
    · let R := F.erase k
      have size : R.card + 1 = F.card := card_erase_add_one hit
      have vr : ∀ i ∈ R, i < k := by
        intro i hi
        obtain ⟨ne,h⟩ := mem_erase.mp hi
        have := valid i h
        dsimp [k] at *; omega
      have ir : ∀ i ∈ R, W i ⊆ T := fun i hi => inside i (mem_of_mem_erase hi)
      have eq : F = insert k R := (insert_erase hit).symm
      by_cases big : 1 < (W k).card
      · obtain ⟨a,b,ha,hb,e⟩ := gate s (by omega)
        let G := insert a (insert b R)
        have step := prev G (by
          intro i hi
          simp only [G, mem_insert] at hi
          rcases hi with rfl|rfl|h
          · exact ha
          · exact hb
          · exact vr _ h) (by
          have h := inside k hit
          rw [show W k = W a ∪ W b from e] at h
          intro i hi
          simp only [G, mem_insert] at hi
          rcases hi with rfl|rfl|hi
          · exact (subset_union_left).trans h
          · exact (subset_union_right).trans h
          · exact ir _ hi)
        change (G.biUnion W).card ≤ G.card + c at step
        have same : F.biUnion W = G.biUnion W := by
          rw [eq,biUnion_insert,show W k = W a ∪ W b from e]
          simp [G,union_assoc]
        have c1 := card_insert_le a (insert b R)
        have c2 := card_insert_le b R
        have hs : good s := ⟨big,inside k hit⟩
        rw [same,ite_eq_left hs]; dsimp [G] at step ⊢; omega
      · have step := prev R vr ir
        change (R.biUnion W).card ≤ R.card+c at step
        have add := card_union_le (W k) (R.biUnion W)
        rw [eq,biUnion_insert]
        have fresh : k ∉ R := notMem_erase _ _
        rw [card_insert_of_notMem fresh]
        omega
    · have v : ∀ i ∈ F, i < n+s := by
        intro i hi
        have := valid i hi
        have ne : i ≠ k := fun e => hit (e ▸ hi)
        dsimp [k] at ne; omega
      have step := prev F v inside
      change (F.biUnion W).card ≤ F.card+c at step
      omega

-- The sum is over distinct centers. A nontrivial shared union can belong
-- to only one neighborhood, even if several terms use the same center.
theorem star_leaf_count {V : Type*} [DecidableEq V] (n s m : ℕ)
    (W : ℕ → Finset V) (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (hood : V → Finset V) (thin : ∀ a b, a ≠ b → (hood a ∩ hood b).card ≤ 1)
    (center : Fin m → V) (arm : Fin m → ℕ) (valid : ∀ j, arm j < n+s)
    (sound : ∀ j, W (arm j) ⊆ hood (center j)) :
    let centers := univ.image center
    let arms := fun c => (univ.filter fun j => center j = c).image arm
    ∑ c ∈ centers, ((arms c).biUnion W).card ≤ m+s := by
  classical
  intro centers arms
  let active := fun c => (range s).filter fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ hood c
  have each (c) : ((arms c).biUnion W).card ≤
      (univ.filter fun j => center j = c).card + (active c).card := by
    apply le_trans (leaves_le n s W raw gate (hood c) (arms c) ?_ ?_)
    · exact Nat.add_le_add_right card_image_le _
    · intro i hi
      obtain ⟨j,_,rfl⟩ := mem_image.mp hi
      exact valid _
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      rw [←(mem_filter.mp hj).2]
      exact sound _
  have disj : (centers : Set V).PairwiseDisjoint active := by
    intro a _ b _ ne
    apply disjoint_left.mpr
    intro j ja jb
    obtain ⟨_,big,ha⟩ := mem_filter.mp ja
    obtain ⟨_,_,hb⟩ := mem_filter.mp jb
    exact (Nat.not_lt_of_ge ((card_le_card (subset_inter ha hb)).trans (thin a b ne))) big
  have total : ∑ c ∈ centers, (active c).card ≤ s := by
    rw [←card_biUnion disj]
    apply le_trans (card_le_card (t := range s) ?_) (by simp)
    intro j h
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hc).1
  calc
    _ ≤ _ := sum_le_sum (fun c _ => each c)
    _ = _ := sum_add_distrib
    _ ≤ m+s := by
      rw [sum_card_fiberwise_eq_card_filter]
      have h := card_le_card (filter_subset (fun i => center i ∈ centers) (univ : Finset (Fin m)))
      simp only [card_univ,Fintype.card_fin] at h
      omega
end PEqualNP.Research.StarNetworks

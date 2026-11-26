import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! Shared union counting reuses the two generic lemmas from dlidar's
research/L-meta-4675-star-networks, commit 4232fe6f4de0011cf815420c113db3accc2ac2c1.
The remaining results specialize the count to the punctured plane with two marked outputs. -/
namespace PEqualNP.Research.Shared7368
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

abbrev V := Fin 26
def key (a b : V) : Finset V := {a,b}
def original : Finset (Finset V) := {key 0 12,key 0 14,key 0 20,key 1 13,key 1 19,key 1 23,key 2 12,key 2 18,key 2 22,key 2 23,key 3 17,key 3 21,key 3 22,key 4 16,key 4 20,key 4 21,key 4 23,key 5 15,key 5 19,key 5 20,key 5 22,key 6 14,key 6 18,key 6 19,key 6 21,key 7 13,key 7 17,key 7 18,key 7 20,key 8 12,key 8 16,key 8 17,key 8 19,key 9 14,key 9 15,key 9 17,key 9 23,key 10 13,key 10 14,key 10 16,key 10 22,key 11 12,key 11 13,key 11 15,key 11 21}
def markedA : Finset V := {0,1,3}
def markedB : Finset V := {15,16,18}
def augmented := original ∪ markedA.image (key 24) ∪ markedB.image (key 25)
def hood (u : V) : Finset V := univ.filter fun v => key u v ∈ augmented
def matching : Fin 12 → Finset V := ![key 0 14, key 1 13, key 2 23, key 3 22, key 4 20, key 5 19, key 6 21, key 7 18, key 8 17, key 9 15, key 10 16, key 11 12]
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
theorem augmented_card : augmented.card = 51 := by decide +kernel
theorem matching_edges : ∀ p, matching p ∈ original := by decide +kernel
theorem matching_unique : ∀ (p q : Fin 12) (v : V), v ∈ matching p → v ∈ matching q → p = q := by decide +kernel
def neighbours : V → Finset V := ![{12,14,20,24}, {13,19,23,24}, {12,18,22,23}, {17,21,22,24}, {16,20,21,23}, {15,19,20,22}, {14,18,19,21}, {13,17,18,20}, {12,16,17,19}, {14,15,17,23}, {13,14,16,22}, {12,13,15,21}, {0,2,8,11}, {1,7,10,11}, {0,6,9,10}, {5,9,11,25}, {4,8,10,25}, {3,7,8,9}, {2,6,7,25}, {1,5,6,8}, {0,4,5,7}, {3,4,6,11}, {2,3,5,10}, {1,2,4,9}, {0,1,3}, {15,16,18}]
theorem neighbours_exact : ∀ u v : V, v ∈ neighbours u ↔ key u v ∈ augmented := by decide +kernel
theorem thin : ∀ u v : V, u ≠ v → (neighbours u ∩ neighbours v).card ≤ 1 := by decide +kernel

theorem count_shared (n s m : ℕ) (W : ℕ → Finset V)
    (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (center : Fin (m+2) → V) (arm : Fin (m+2) → ℕ)
    (valid : ∀ i, arm i < n+s)
    (sound : ∀ i, W (arm i) ⊆ neighbours (center i))
    (cover : ∀ e ∈ original, ∃ i : Fin m, ∃ v ∈ W (arm (Fin.castAdd 2 i)), key (center (Fin.castAdd 2 i)) v = e)
    (monA : ∃ i, center i = 24 ∧ W (arm i) = markedA)
    (monB : ∃ i, center i = 25 ∧ W (arm i) = markedB) :
    60 ≤ s + m + (m-1) := by
  classical
  choose f v hv he using fun p => cover (matching p) (matching_edges p)
  have fc (p) : center (Fin.castAdd 2 (f p)) ∈ matching p := by
    rw [← he p]; simp [key]
  have inject : Function.Injective f := by
    intro p q h
    exact matching_unique p q _ (fc p) (h.symm ▸ fc q)
  have terms : 12 ≤ m := by simpa using Fintype.card_le_of_injective f inject
  let centers := univ.image center
  let arms := fun c => (univ.filter fun i => center i = c).image arm
  let leaves := fun c => (arms c).biUnion W
  have total := star_leaf_count n s (m+2) W raw gate neighbours thin center arm valid sound
  change ∑ c ∈ centers, (leaves c).card ≤ m+2+s at total
  have all : ∀ e ∈ augmented, ∃ i, ∃ v ∈ W (arm i), key (center i) v = e := by
    intro e h
    rcases mem_union.mp h with ab|hb
    · rcases mem_union.mp ab with h0|ha
      · obtain ⟨j,v,hv,he⟩ := cover e h0
        exact ⟨_,v,hv,he⟩
      · obtain ⟨i,hi,hw⟩ := monA
        obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
        exact ⟨i,v,hw.symm ▸ hv,by rw [hi]⟩
    · obtain ⟨i,hi,hw⟩ := monB
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
      exact ⟨i,v,hw.symm ▸ hv,by rw [hi]⟩
  have sub : augmented ⊆ centers.biUnion (fun c => (leaves c).image (key c)) := by
    intro e h
    obtain ⟨i,v,hv,he⟩ := all e h
    apply mem_biUnion.mpr
    refine ⟨center i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_image.mpr ⟨v,?_,he⟩⟩
    exact mem_biUnion.mpr ⟨arm i,mem_image.mpr ⟨i,by simp,rfl⟩,hv⟩
  have size : augmented.card ≤ ∑ c ∈ centers, (leaves c).card :=
    ((card_le_card sub).trans card_biUnion_le).trans (sum_le_sum fun _ _ => card_image_le)
  rw [augmented_card] at size
  omega

-- Singletons are all rejecting graph inputs. An OR-only wire is consequently
-- forced to have exactly the indicated raw support even when its value on
-- inputs containing an edge is unspecified.
theorem mask_identified {α : Type*} [DecidableEq α] (W T : Finset α)
    (h : ∀ i, (({i} : Finset α) ∩ W).Nonempty ↔ (({i} : Finset α) ∩ T).Nonempty) :
    W = T := by
  ext i
  have test := h i
  simpa [Finset.Nonempty] using test

#print axioms mask_identified
#print axioms leaves_le
#print axioms star_leaf_count
#print axioms augmented_card
#print axioms matching_edges
#print axioms matching_unique
#print axioms neighbours_exact
#print axioms thin
#print axioms count_shared
end PEqualNP.Research.Shared7368

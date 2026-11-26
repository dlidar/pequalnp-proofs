import PEqualNP.Research.Overlap6752

namespace PEqualNP.Research.Rectangle6752

open PEqualNP.Research.Residual6752
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_8005

abbrev V := Fin 11

def row (L : Finset V) (v : V) := (L.filter (graph.Adj v)).card

-- A threshold on row degrees gives a dual certificate for every possible right side.
theorem threshold (L R : Finset V) (dis : Disjoint L R) (q : Nat) :
    ∑ v ∈ R, row L v ≤ R.card * q + ∑ v ∈ Finset.univ \ L, (row L v - q) := by
  have sub : R ⊆ Finset.univ \ L := fun v hv => Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, fun hl => Finset.disjoint_left.mp dis hl hv⟩
  calc
    _ ≤ ∑ v ∈ R, (q + (row L v - q)) := Finset.sum_le_sum fun _ _ => by omega
    _ = R.card * q + ∑ v ∈ R, (row L v - q) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg sub (by simp)) _

def maximum : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 6
  | 4 => 9
  | _ => 11

def rowBound (L : Finset V) : Prop :=
  L.card ≤ 5 → ∃ q : Fin 6, L.card * q.val + ∑ v ∈ Finset.univ \ L, (row L v - q.val) ≤ maximum L.card

-- A binary tree enumerates vertex subsets. The predicate is tested at its leaves.
def allSubsets (p : Finset V → Bool) : List V → Finset V → Bool
  | [], acc => p acc
  | a :: l, acc => allSubsets p l acc && allSubsets p l (insert a acc)

theorem allSubsets_sound (p : Finset V → Bool) (l : List V) (s acc : Finset V)
    (hs : s ⊆ l.toFinset) (checked : allSubsets p l acc = true) : p (acc ∪ s) = true := by
  induction l generalizing s acc with
  | nil =>
    have : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun _ hi => by simpa using hs hi)
    subst s; simpa [allSubsets] using checked
  | cons a l ih =>
    obtain ⟨h₀,h₁⟩ := Bool.and_eq_true_iff.mp checked
    by_cases h : a ∈ s
    · have incl : s.erase a ⊆ l.toFinset := by
        intro i hi
        simpa [Finset.ne_of_mem_erase hi] using hs (Finset.mem_of_mem_erase hi)
      have r := ih (s.erase a) (insert a acc) incl h₁
      have eq : insert a acc ∪ s.erase a = acc ∪ s := by
        ext i; by_cases e : i = a
        · subst i; simp [h]
        · simp [e]
      rwa [eq] at r
    · apply ih s acc _ h₀
      intro i hi
      have ne : i ≠ a := fun eq => h (eq ▸ hi)
      simpa [ne] using hs hi

instance (L : Finset V) : Decidable (rowBound L) := by unfold rowBound; infer_instance
def good (L : Finset V) : Bool := decide (rowBound L)
def vertices : List V := [0,1,2,3,4,5,6,7,8,9,10]

set_option maxHeartbeats 3000000

set_option maxRecDepth 20000

private theorem row_5_0 : allSubsets good [5,6,7,8,9,10] ∅ = true := by decide +kernel

private theorem row_5_16 : allSubsets good [5,6,7,8,9,10] (insert 4 ∅) = true := by decide +kernel

private theorem row_4_0 : allSubsets good [4,5,6,7,8,9,10] ∅ = true := Bool.and_eq_true_iff.mpr ⟨row_5_0,row_5_16⟩

private theorem row_5_8 : allSubsets good [5,6,7,8,9,10] (insert 3 ∅) = true := by decide +kernel

private theorem row_5_24 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 ∅)) = true := by decide +kernel

private theorem row_4_8 : allSubsets good [4,5,6,7,8,9,10] (insert 3 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_5_8,row_5_24⟩

private theorem row_3_0 : allSubsets good [3,4,5,6,7,8,9,10] ∅ = true := Bool.and_eq_true_iff.mpr ⟨row_4_0,row_4_8⟩

private theorem row_5_4 : allSubsets good [5,6,7,8,9,10] (insert 2 ∅) = true := by decide +kernel

private theorem row_5_20 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 2 ∅)) = true := by decide +kernel

private theorem row_4_4 : allSubsets good [4,5,6,7,8,9,10] (insert 2 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_5_4,row_5_20⟩

private theorem row_5_12 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 2 ∅)) = true := by decide +kernel

private theorem row_5_28 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 2 ∅))) = true := by decide +kernel

private theorem row_4_12 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 2 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_12,row_5_28⟩

private theorem row_3_4 : allSubsets good [3,4,5,6,7,8,9,10] (insert 2 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_4_4,row_4_12⟩

private theorem row_2_0 : allSubsets good [2,3,4,5,6,7,8,9,10] ∅ = true := Bool.and_eq_true_iff.mpr ⟨row_3_0,row_3_4⟩

private theorem row_5_2 : allSubsets good [5,6,7,8,9,10] (insert 1 ∅) = true := by decide +kernel

private theorem row_5_18 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 1 ∅)) = true := by decide +kernel

private theorem row_4_2 : allSubsets good [4,5,6,7,8,9,10] (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_5_2,row_5_18⟩

private theorem row_5_10 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 1 ∅)) = true := by decide +kernel

private theorem row_5_26 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 1 ∅))) = true := by decide +kernel

private theorem row_4_10 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_10,row_5_26⟩

private theorem row_3_2 : allSubsets good [3,4,5,6,7,8,9,10] (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_4_2,row_4_10⟩

private theorem row_5_6 : allSubsets good [5,6,7,8,9,10] (insert 2 (insert 1 ∅)) = true := by decide +kernel

private theorem row_5_22 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 2 (insert 1 ∅))) = true := by decide +kernel

private theorem row_4_6 : allSubsets good [4,5,6,7,8,9,10] (insert 2 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_6,row_5_22⟩

private theorem row_5_14 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 2 (insert 1 ∅))) = true := by decide +kernel

private theorem row_5_30 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 2 (insert 1 ∅)))) = true := by decide +kernel

private theorem row_4_14 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 2 (insert 1 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨row_5_14,row_5_30⟩

private theorem row_3_6 : allSubsets good [3,4,5,6,7,8,9,10] (insert 2 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_4_6,row_4_14⟩

private theorem row_2_2 : allSubsets good [2,3,4,5,6,7,8,9,10] (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_3_2,row_3_6⟩

private theorem row_1_0 : allSubsets good [1,2,3,4,5,6,7,8,9,10] ∅ = true := Bool.and_eq_true_iff.mpr ⟨row_2_0,row_2_2⟩

private theorem row_5_1 : allSubsets good [5,6,7,8,9,10] (insert 0 ∅) = true := by decide +kernel

private theorem row_5_17 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 0 ∅)) = true := by decide +kernel

private theorem row_4_1 : allSubsets good [4,5,6,7,8,9,10] (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_5_1,row_5_17⟩

private theorem row_5_9 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 0 ∅)) = true := by decide +kernel

private theorem row_5_25 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 0 ∅))) = true := by decide +kernel

private theorem row_4_9 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_9,row_5_25⟩

private theorem row_3_1 : allSubsets good [3,4,5,6,7,8,9,10] (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_4_1,row_4_9⟩

private theorem row_5_5 : allSubsets good [5,6,7,8,9,10] (insert 2 (insert 0 ∅)) = true := by decide +kernel

private theorem row_5_21 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 2 (insert 0 ∅))) = true := by decide +kernel

private theorem row_4_5 : allSubsets good [4,5,6,7,8,9,10] (insert 2 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_5,row_5_21⟩

private theorem row_5_13 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 2 (insert 0 ∅))) = true := by decide +kernel

private theorem row_5_29 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 2 (insert 0 ∅)))) = true := by decide +kernel

private theorem row_4_13 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 2 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨row_5_13,row_5_29⟩

private theorem row_3_5 : allSubsets good [3,4,5,6,7,8,9,10] (insert 2 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_4_5,row_4_13⟩

private theorem row_2_1 : allSubsets good [2,3,4,5,6,7,8,9,10] (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_3_1,row_3_5⟩

private theorem row_5_3 : allSubsets good [5,6,7,8,9,10] (insert 1 (insert 0 ∅)) = true := by decide +kernel

private theorem row_5_19 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem row_4_3 : allSubsets good [4,5,6,7,8,9,10] (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_5_3,row_5_19⟩

private theorem row_5_11 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem row_5_27 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem row_4_11 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨row_5_11,row_5_27⟩

private theorem row_3_3 : allSubsets good [3,4,5,6,7,8,9,10] (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_4_3,row_4_11⟩

private theorem row_5_7 : allSubsets good [5,6,7,8,9,10] (insert 2 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem row_5_23 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 2 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem row_4_7 : allSubsets good [4,5,6,7,8,9,10] (insert 2 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨row_5_7,row_5_23⟩

private theorem row_5_15 : allSubsets good [5,6,7,8,9,10] (insert 3 (insert 2 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem row_5_31 : allSubsets good [5,6,7,8,9,10] (insert 4 (insert 3 (insert 2 (insert 1 (insert 0 ∅))))) = true := by decide +kernel

private theorem row_4_15 : allSubsets good [4,5,6,7,8,9,10] (insert 3 (insert 2 (insert 1 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨row_5_15,row_5_31⟩

private theorem row_3_7 : allSubsets good [3,4,5,6,7,8,9,10] (insert 2 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨row_4_7,row_4_15⟩

private theorem row_2_3 : allSubsets good [2,3,4,5,6,7,8,9,10] (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨row_3_3,row_3_7⟩

private theorem row_1_1 : allSubsets good [1,2,3,4,5,6,7,8,9,10] (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨row_2_1,row_2_3⟩

private theorem row_0_0 : allSubsets good [0,1,2,3,4,5,6,7,8,9,10] ∅ = true := Bool.and_eq_true_iff.mpr ⟨row_1_0,row_1_1⟩

theorem check_root : allSubsets good vertices ∅ = true := row_0_0

theorem rows_certified (L : Finset V) : rowBound L := by
  have sub : L ⊆ vertices.toFinset := fun i _ => (by decide : ∀ i, i ∈ vertices.toFinset) i
  have h := allSubsets_sound good vertices L ∅ sub check_root
  simpa only [Finset.empty_union,good,decide_eq_true_eq] using h

theorem disjoint_edges (L R : Finset V) (dis : Disjoint L R)
    (size : R.card = L.card) (small : L.card ≤ 5) :
    ∑ v ∈ R, row L v ≤ maximum L.card := by
  obtain ⟨q,h⟩ := rows_certified L small
  have bound := threshold L R dis q.val
  rw [size] at bound
  exact bound.trans h

-- Oriented pairs from disjoint sides identify distinct unordered inputs.
def crossNeg (L R : Finset V) :=
  (R ×ˢ L).filter fun p => ¬ graph.Adj p.1 p.2

theorem count_crossNeg (L R : Finset V) :
    (crossNeg L R).card + ∑ v ∈ R, row L v = R.card * L.card := by
  have eq : crossNeg L R = R.biUnion (fun v =>
      ((L.filter fun u => ¬graph.Adj v u).image fun u => (v,u))) := by
    ext ⟨a,b⟩
    simp [crossNeg, and_assoc, and_left_comm, and_comm]
  rw [eq,Finset.card_biUnion]
  · rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v ∈ R, L.card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.snd he)]
        simpa [row, Nat.add_comm] using Finset.card_filter_add_card_filter_not (s := L) (graph.Adj v)
      _ = _ := by simp
  · intro a _ b _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨u,_,eq⟩ := Finset.mem_image.mp hp
    obtain ⟨v,_,eq'⟩ := Finset.mem_image.mp hq
    exact hne (congrArg Prod.fst (eq.trans eq'.symm))

theorem false_pairs (L R : Finset V) (dis : Disjoint L R) (size : R.card = L.card)
    (small : L.card ≤ 5) : L.card * L.card - maximum L.card ≤ (crossNeg L R).card := by
  have a := count_crossNeg L R
  rw [size] at a
  have b := disjoint_edges L R dis size small
  omega

end PEqualNP.Research.Rectangle6752

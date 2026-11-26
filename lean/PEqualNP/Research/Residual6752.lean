import PEqualNP.Defs

namespace PEqualNP.Research.Residual6752

open PEqualNP.EdgeOwnership PEqualNP.TopForm
abbrev Edge := Sym2 (Fin 11)

abbrev graph := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def edge : Fin 16 → Edge
  | 0 => s(0,9)
  | 1 => s(0,10)
  | 2 => s(1,4)
  | 3 => s(1,8)
  | 4 => s(2,5)
  | 5 => s(2,10)
  | 6 => s(3,6)
  | 7 => s(3,7)
  | 8 => s(4,8)
  | 9 => s(4,10)
  | 10 => s(5,8)
  | 11 => s(5,9)
  | 12 => s(6,7)
  | 13 => s(6,10)
  | 14 => s(7,9)
  | _ => s(8,9)

def block : Fin 14 → Finset (Fin 16)
  | 0 => {0,1}
  | 1 => {2,3}
  | 2 => {4,5}
  | 3 => {6,7}
  | 4 => {2,8,9}
  | 5 => {4,10,11}
  | 6 => {6,12,13}
  | 7 => {7,12,14}
  | 8 => {3,8,10,15}
  | 9 => {0,11,14,15}
  | 10 => {1,5,9,13}
  | 11 => {2,3,8}
  | 12 => {6,7,12}
  | _ => {10,11,15}

theorem edge_injective : Function.Injective edge := by
  intro x y
  exact (by decide +kernel : ∀ a b, edge a = edge b → a = b) x y

theorem edge_list : Finset.univ.image edge = graph.edgeFinset := by decide +kernel

theorem star_incidence : ∀ (v : Fin 11) (i : Fin 16),
    i ∈ block (v.castLE (by decide)) ↔ v ∈ edge i := by decide +kernel

theorem triangles :
    (block 11).image edge = {s(1,4), s(1,8), s(4,8)} ∧
    (block 12).image edge = {s(3,6), s(3,7), s(6,7)} ∧
    (block 13).image edge = {s(5,8), s(5,9), s(8,9)} := by decide +kernel

def capacity : Nat → Nat
  | 0 => 0
  | 1 => 4
  | 2 => 8
  | 3 => 11
  | 4 => 14
  | _ => 16

def starCapacity : Nat → Nat
  | 0 => 0
  | 1 => 4
  | 2 => 8
  | 3 => 11
  | 4 => 13
  | 5 => 14
  | 6 => 15
  | _ => 16

def indexList : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

-- Every subfamily is visited once, carrying its size and union of edge indices.
def verify (p : Nat → Finset (Fin 16) → Finset (Fin 14) → Bool) :
    List (Fin 14) → Nat → Finset (Fin 16) → Finset (Fin 14) → Bool
  | [], k, u, s => p k u s
  | a :: l, k, u, s => verify p l k u s &&
      verify p l (k+1) (u ∪ block a) (insert a s)

theorem verify_sound (p : Nat → Finset (Fin 16) → Finset (Fin 14) → Bool)
    (l : List (Fin 14)) (s : Finset (Fin 14)) (sub : s ⊆ l.toFinset)
    (k : Nat) (u : Finset (Fin 16)) (seen : Finset (Fin 14)) (nd : l.Nodup)
    (h : verify p l k u seen = true) :
    p (k+s.card) (u ∪ s.biUnion block) (seen ∪ s) = true := by
  induction l generalizing s k u seen with
  | nil =>
    have : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by simpa using sub hi)
    subst s
    simpa [verify] using h
  | cons a l ih =>
    obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp nd
    by_cases hs : a ∈ s
    · have sub' : s.erase a ⊆ l.toFinset := by
        intro i hi
        have := sub (Finset.mem_of_mem_erase hi)
        simpa [Finset.ne_of_mem_erase hi] using this
      have hv := ih (s.erase a) sub' (k+1) (u ∪ block a) (insert a seen) hl h1
      have eq := Finset.insert_erase hs
      have c := Finset.card_erase_add_one hs
      have un : block a ∪ (s.erase a).biUnion block = s.biUnion block := by
        rw [← Finset.biUnion_insert,eq]
      have us : insert a seen ∪ s.erase a = seen ∪ s := by
        ext i
        by_cases e : i = a
        · subst i; simp [hs]
        · simp [e]
      rw [Finset.union_assoc,un,us] at hv
      have cnt : k + 1 + (s.erase a).card = k + s.card := by omega
      rwa [cnt] at hv
    · have sub' : s ⊆ l.toFinset := by
        intro i hi
        have hn : i ≠ a := fun e => hs (e ▸ hi)
        simpa [hn] using sub hi
      exact ih s sub' k u seen hl h0

def boundTest (k : Nat) (u : Finset (Fin 16)) (s : Finset (Fin 14)) : Bool :=
  decide (u.card ≤ capacity k ∧
    ((∀ a ∈ s, a.val < 11) → u.card ≤ starCapacity k) ∧
    (k = 5 → u.card = 16 → s = {5,9,10,11,12}))

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
private theorem check_6_0 : verify boundTest [6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := by decide +kernel

private theorem check_6_32 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 5) (insert 5 ∅) = true := by decide +kernel

private theorem check_5_0 : verify boundTest [5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_6_0, check_6_32⟩

private theorem check_6_16 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 4) (insert 4 ∅) = true := by decide +kernel

private theorem check_6_48 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 4) ∪ block 5) (insert 5 (insert 4 ∅)) = true := by decide +kernel

private theorem check_5_16 : verify boundTest [5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 4) (insert 4 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_6_16, check_6_48⟩

private theorem check_4_0 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_5_0, check_5_16⟩

private theorem check_6_8 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 3) (insert 3 ∅) = true := by decide +kernel

private theorem check_6_40 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 3) ∪ block 5) (insert 5 (insert 3 ∅)) = true := by decide +kernel

private theorem check_5_8 : verify boundTest [5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 3) (insert 3 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_6_8, check_6_40⟩

private theorem check_6_24 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 3) ∪ block 4) (insert 4 (insert 3 ∅)) = true := by decide +kernel

private theorem check_6_56 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 ∅))) = true := by decide +kernel

private theorem check_5_24 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 3) ∪ block 4) (insert 4 (insert 3 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_24, check_6_56⟩

private theorem check_4_8 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 3) (insert 3 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_5_8, check_5_24⟩

private theorem check_3_0 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_4_0, check_4_8⟩

private theorem check_6_4 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 2) (insert 2 ∅) = true := by decide +kernel

private theorem check_6_36 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 5) (insert 5 (insert 2 ∅)) = true := by decide +kernel

private theorem check_5_4 : verify boundTest [5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 2) (insert 2 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_6_4, check_6_36⟩

private theorem check_6_20 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 4) (insert 4 (insert 2 ∅)) = true := by decide +kernel

private theorem check_6_52 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 2) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 2 ∅))) = true := by decide +kernel

private theorem check_5_20 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 4) (insert 4 (insert 2 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_20, check_6_52⟩

private theorem check_4_4 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 2) (insert 2 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_5_4, check_5_20⟩

private theorem check_6_12 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 3) (insert 3 (insert 2 ∅)) = true := by decide +kernel

private theorem check_6_44 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 2) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 2 ∅))) = true := by decide +kernel

private theorem check_5_12 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 3) (insert 3 (insert 2 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_12, check_6_44⟩

private theorem check_6_28 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 ∅))) = true := by decide +kernel

private theorem check_6_60 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 2) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 2 ∅)))) = true := by decide +kernel

private theorem check_5_28 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_28, check_6_60⟩

private theorem check_4_12 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 2) ∪ block 3) (insert 3 (insert 2 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_12, check_5_28⟩

private theorem check_3_4 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 2) (insert 2 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_4_4, check_4_12⟩

private theorem check_2_0 : verify boundTest [2,3,4,5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_3_0, check_3_4⟩

private theorem check_6_2 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 1) (insert 1 ∅) = true := by decide +kernel

private theorem check_6_34 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 5) (insert 5 (insert 1 ∅)) = true := by decide +kernel

private theorem check_5_2 : verify boundTest [5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 1) (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_6_2, check_6_34⟩

private theorem check_6_18 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 4) (insert 4 (insert 1 ∅)) = true := by decide +kernel

private theorem check_6_50 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 1 ∅))) = true := by decide +kernel

private theorem check_5_18 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 4) (insert 4 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_18, check_6_50⟩

private theorem check_4_2 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 1) (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_5_2, check_5_18⟩

private theorem check_6_10 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 3) (insert 3 (insert 1 ∅)) = true := by decide +kernel

private theorem check_6_42 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 1 ∅))) = true := by decide +kernel

private theorem check_5_10 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 3) (insert 3 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_10, check_6_42⟩

private theorem check_6_26 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 1 ∅))) = true := by decide +kernel

private theorem check_6_58 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 1) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 1 ∅)))) = true := by decide +kernel

private theorem check_5_26 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 1 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_26, check_6_58⟩

private theorem check_4_10 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 3) (insert 3 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_10, check_5_26⟩

private theorem check_3_2 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 1) (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_4_2, check_4_10⟩

private theorem check_6_6 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 2) (insert 2 (insert 1 ∅)) = true := by decide +kernel

private theorem check_6_38 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 5) (insert 5 (insert 2 (insert 1 ∅))) = true := by decide +kernel

private theorem check_5_6 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 2) (insert 2 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_6, check_6_38⟩

private theorem check_6_22 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 1 ∅))) = true := by decide +kernel

private theorem check_6_54 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 1) ∪ block 2) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 2 (insert 1 ∅)))) = true := by decide +kernel

private theorem check_5_22 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 1 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_22, check_6_54⟩

private theorem check_4_6 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 2) (insert 2 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_6, check_5_22⟩

private theorem check_6_14 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 ∅))) = true := by decide +kernel

private theorem check_6_46 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 2 (insert 1 ∅)))) = true := by decide +kernel

private theorem check_5_14 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_14, check_6_46⟩

private theorem check_6_30 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 1 ∅)))) = true := by decide +kernel

private theorem check_6_62 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 2 (insert 1 ∅))))) = true := by decide +kernel

private theorem check_5_30 : verify boundTest [5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 1 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_30, check_6_62⟩

private theorem check_4_14 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_5_14, check_5_30⟩

private theorem check_3_6 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 1) ∪ block 2) (insert 2 (insert 1 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_4_6, check_4_14⟩

private theorem check_2_2 : verify boundTest [2,3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 1) (insert 1 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_3_2, check_3_6⟩

private theorem check_1_0 : verify boundTest [1,2,3,4,5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_2_0, check_2_2⟩

private theorem check_6_1 : verify boundTest [6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := by decide +kernel

private theorem check_6_33 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 5) (insert 5 (insert 0 ∅)) = true := by decide +kernel

private theorem check_5_1 : verify boundTest [5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_6_1, check_6_33⟩

private theorem check_6_17 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 4) (insert 4 (insert 0 ∅)) = true := by decide +kernel

private theorem check_6_49 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 0 ∅))) = true := by decide +kernel

private theorem check_5_17 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 4) (insert 4 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_17, check_6_49⟩

private theorem check_4_1 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_5_1, check_5_17⟩

private theorem check_6_9 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 3) (insert 3 (insert 0 ∅)) = true := by decide +kernel

private theorem check_6_41 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 0 ∅))) = true := by decide +kernel

private theorem check_5_9 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 3) (insert 3 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_9, check_6_41⟩

private theorem check_6_25 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_57 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_25 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_25, check_6_57⟩

private theorem check_4_9 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 3) (insert 3 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_9, check_5_25⟩

private theorem check_3_1 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_4_1, check_4_9⟩

private theorem check_6_5 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 2) (insert 2 (insert 0 ∅)) = true := by decide +kernel

private theorem check_6_37 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 5) (insert 5 (insert 2 (insert 0 ∅))) = true := by decide +kernel

private theorem check_5_5 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 2) (insert 2 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_5, check_6_37⟩

private theorem check_6_21 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_53 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 2) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 2 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_21 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_21, check_6_53⟩

private theorem check_4_5 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 2) (insert 2 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_5, check_5_21⟩

private theorem check_6_13 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_45 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 2) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 2 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_13 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_13, check_6_45⟩

private theorem check_6_29 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_6_61 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 2) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 2 (insert 0 ∅))))) = true := by decide +kernel

private theorem check_5_29 : verify boundTest [5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_29, check_6_61⟩

private theorem check_4_13 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_5_13, check_5_29⟩

private theorem check_3_5 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 2) (insert 2 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_4_5, check_4_13⟩

private theorem check_2_1 : verify boundTest [2,3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_3_1, check_3_5⟩

private theorem check_6_3 : verify boundTest [6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 1) (insert 1 (insert 0 ∅)) = true := by decide +kernel

private theorem check_6_35 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 5) (insert 5 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem check_5_3 : verify boundTest [5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 1) (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_6_3, check_6_35⟩

private theorem check_6_19 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 4) (insert 4 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_51 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_19 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 4) (insert 4 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_19, check_6_51⟩

private theorem check_4_3 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 1) (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_5_3, check_5_19⟩

private theorem check_6_11 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 3) (insert 3 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_43 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_11 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 3) (insert 3 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_11, check_6_43⟩

private theorem check_6_27 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_6_59 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 1) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 1 (insert 0 ∅))))) = true := by decide +kernel

private theorem check_5_27 : verify boundTest [5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 1 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_27, check_6_59⟩

private theorem check_4_11 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 3) (insert 3 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_5_11, check_5_27⟩

private theorem check_3_3 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 1) (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_4_3, check_4_11⟩

private theorem check_6_7 : verify boundTest [6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 2) (insert 2 (insert 1 (insert 0 ∅))) = true := by decide +kernel

private theorem check_6_39 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 5) (insert 5 (insert 2 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_5_7 : verify boundTest [5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 2) (insert 2 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_7, check_6_39⟩

private theorem check_6_23 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_6_55 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 2 (insert 1 (insert 0 ∅))))) = true := by decide +kernel

private theorem check_5_23 : verify boundTest [5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 4) (insert 4 (insert 2 (insert 1 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_23, check_6_55⟩

private theorem check_4_7 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 2) (insert 2 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_5_7, check_5_23⟩

private theorem check_6_15 : verify boundTest [6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 (insert 0 ∅)))) = true := by decide +kernel

private theorem check_6_47 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 5) (insert 5 (insert 3 (insert 2 (insert 1 (insert 0 ∅))))) = true := by decide +kernel

private theorem check_5_15 : verify boundTest [5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_15, check_6_47⟩

private theorem check_6_31 : verify boundTest [6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 1 (insert 0 ∅))))) = true := by decide +kernel

private theorem check_6_63 : verify boundTest [6,7,8,9,10,11,12,13] 6 ((((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) ∪ block 5) (insert 5 (insert 4 (insert 3 (insert 2 (insert 1 (insert 0 ∅)))))) = true := by decide +kernel

private theorem check_5_31 : verify boundTest [5,6,7,8,9,10,11,12,13] 5 (((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) ∪ block 4) (insert 4 (insert 3 (insert 2 (insert 1 (insert 0 ∅))))) = true := Bool.and_eq_true_iff.mpr ⟨check_6_31, check_6_63⟩

private theorem check_4_15 : verify boundTest [4,5,6,7,8,9,10,11,12,13] 4 ((((∅ ∪ block 0) ∪ block 1) ∪ block 2) ∪ block 3) (insert 3 (insert 2 (insert 1 (insert 0 ∅)))) = true := Bool.and_eq_true_iff.mpr ⟨check_5_15, check_5_31⟩

private theorem check_3_7 : verify boundTest [3,4,5,6,7,8,9,10,11,12,13] 3 (((∅ ∪ block 0) ∪ block 1) ∪ block 2) (insert 2 (insert 1 (insert 0 ∅))) = true := Bool.and_eq_true_iff.mpr ⟨check_4_7, check_4_15⟩

private theorem check_2_3 : verify boundTest [2,3,4,5,6,7,8,9,10,11,12,13] 2 ((∅ ∪ block 0) ∪ block 1) (insert 1 (insert 0 ∅)) = true := Bool.and_eq_true_iff.mpr ⟨check_3_3, check_3_7⟩

private theorem check_1_1 : verify boundTest [1,2,3,4,5,6,7,8,9,10,11,12,13] 1 (∅ ∪ block 0) (insert 0 ∅) = true := Bool.and_eq_true_iff.mpr ⟨check_2_1, check_2_3⟩

private theorem check_0_0 : verify boundTest [0,1,2,3,4,5,6,7,8,9,10,11,12,13] 0 ∅ ∅ = true := Bool.and_eq_true_iff.mpr ⟨check_1_0, check_1_1⟩

theorem checked : verify boundTest indexList 0 ∅ ∅ = true := check_0_0

theorem capacities (s : Finset (Fin 14)) :
    (s.biUnion block).card ≤ capacity s.card ∧
    ((∀ a ∈ s, a.val < 11) → (s.biUnion block).card ≤ starCapacity s.card) ∧
    (s.card = 5 → (s.biUnion block).card = 16 → s = {5,9,10,11,12}) := by
  have hs : s ⊆ indexList.toFinset := fun i _ => (by decide : ∀ i, i ∈ indexList.toFinset) i
  apply of_decide_eq_true
  change boundTest s.card (s.biUnion block) s = true
  simpa only [Nat.zero_add, Finset.empty_union] using verify_sound boundTest indexList s hs 0 ∅ ∅ (by decide) checked


-- The intersection argument below follows upstream reduction R_meta_6752_643 (PR 22237).
theorem block_contains (X : Finset Edge) (inGraph : ∀ {e}, e ∈ X → e ∈ graph.edgeFinset)
    (close : ∀ e ∈ X, ∀ f ∈ X, ¬ Disjoint e.toFinset f.toFinset) :
    ∃ a, X ⊆ (block a).image edge := by
  have classification (a b c : Fin 11) : a ≠ b → a ≠ c → b ≠ c →
      graph.Adj a b → graph.Adj a c → graph.Adj b c →
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(1,4),s(1,8),s(4,8)} ∨
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(3,6),s(3,7),s(6,7)} ∨
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(5,8),s(5,9),s(8,9)} := by
    revert a b c
    decide +kernel

  by_cases centre : ∃ v : Fin 11, ∀ e ∈ X, v ∈ e
  · obtain ⟨v,hv⟩ := centre
    refine ⟨v.castLE (by decide), ?_⟩
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (edge_list.symm ▸ inGraph he)
    exact Finset.mem_image.mpr ⟨i, (star_incidence v i).2 (hv _ he), rfl⟩
  have noCentre := centre
  have intersects {e f : Sym2 (Fin 11)} (he : e ∈ X) (hf : f ∈ X) : ∃ v, v ∈ e ∧ v ∈ f := by
    obtain ⟨v,ve,vf⟩ := Finset.not_disjoint_iff.mp (close e he f hf)
    exact ⟨v,Sym2.mem_toFinset.mp ve,Sym2.mem_toFinset.mp vf⟩
  have meet {a b : Fin 11} {h : Sym2 (Fin 11)} (hab : s(a,b) ∈ X) (hh : h ∈ X) :
      a ∈ h ∨ b ∈ h := by
    obtain ⟨v,hv,vh⟩ := intersects hab hh
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Or.inl vh
    · exact Or.inr vh
  have misses (v : Fin 11) : ∃ f ∈ X, v ∉ f := by
    by_contra! covers
    exact noCentre ⟨v,covers⟩
  obtain ⟨e,he,_⟩ := misses 0
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨f,hf,na⟩ := misses a
    have bf := (meet he hf).resolve_left na
    obtain ⟨c,hfeq⟩ := Sym2.mem_iff_exists.mp bf
    subst f
    have ac : a ≠ c := fun h => na (h ▸ Sym2.mem_mk_right _ _)
    have ab : a ≠ b := fun h => na (h ▸ Sym2.mem_mk_left _ _)
    obtain ⟨d,hd,nb⟩ := misses b
    have ad := (meet he hd).resolve_right nb
    have cd := (meet hf hd).resolve_left nb
    have bc : b ≠ c := fun h => nb (h ▸ cd)
    have deq := (Sym2.mem_and_mem_iff ac).mp ⟨ad,cd⟩
    subst d
    have hab : graph.Adj a b := by simpa using inGraph he
    have hac : graph.Adj a c := by simpa using inGraph hd
    have hbc : graph.Adj b c := by simpa using inGraph hf
    have allThree : ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) ⊆ X := by
      intro ed hed
      simp only [Finset.mem_insert,Finset.mem_singleton] at hed
      rcases hed with rfl | rfl | rfl
      · exact he
      · exact hd
      · exact hf
    have sub : X ⊆ {s(a,b),s(a,c),s(b,c)} := by
      intro ed hed
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_cases ah : a ∈ ed
      · by_cases bh : b ∈ ed
        · exact Or.inl ((Sym2.mem_and_mem_iff ab).mp ⟨ah,bh⟩)
        · exact Or.inr (Or.inl ((Sym2.mem_and_mem_iff ac).mp ⟨ah,(meet hf hed).resolve_left bh⟩))
      · exact Or.inr (Or.inr ((Sym2.mem_and_mem_iff bc).mp
          ⟨(meet he hed).resolve_left ah,(meet hd hed).resolve_left ah⟩))
    have eq : X = {s(a,b),s(a,c),s(b,c)} := Finset.Subset.antisymm sub allThree
    rcases classification a b c ab ac bc hab hac hbc with h | h | h
    · exact ⟨11, (eq.trans (h.trans triangles.1.symm)).subset⟩
    · exact ⟨12, (eq.trans (h.trans triangles.2.1.symm)).subset⟩
    · exact ⟨13, (eq.trans (h.trans triangles.2.2.symm)).subset⟩
theorem capacity_mono : Monotone capacity := by
  intro a b h
  match a, b with
  | 0, _ => simp [capacity]
  | 1, 0 | 2, 0 | 2, 1 | 3, 0 | 3, 1 | 3, 2 | 4, 0 | 4, 1 | 4, 2 | 4, 3 => omega
  | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, _+5 | 2, 2 | 2, 3 | 2, 4 | 2, _+5
  | 3, 3 | 3, 4 | 3, _+5 | 4, 4 | 4, _+5 | _+5, _+5 => simp [capacity]
  | _+5, 0 | _+5, 1 | _+5, 2 | _+5, 3 | _+5, 4 => omega

theorem project_cover {K : Finset ℕ} {X : Finset Edge} {F : ℕ → Finset Edge}
    (a : ℕ → Fin 14) (assigned : ∀ g ∈ K, F g ⊆ (block (a g)).image edge)
    (cover : ∀ e ∈ X, ∃ g ∈ K, e ∈ F g) :
    X.card ≤ ((K.image a).biUnion block).card := by
  have sub : X ⊆ ((K.image a).biUnion block).image edge := by
    intro e he
    obtain ⟨g,hg,hit⟩ := cover e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (assigned g hg hit)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_biUnion.mpr
      ⟨a g, Finset.mem_image_of_mem a hg, hi⟩, rfl⟩
  exact (Finset.card_le_card sub).trans Finset.card_image_le

theorem intersecting_family {K : Finset ℕ} {X : Finset Edge} {F : ℕ → Finset Edge}
    (inside : ∀ g ∈ K, F g ⊆ graph.edgeFinset)
    (close : ∀ g ∈ K, ∀ e ∈ F g, ∀ f ∈ F g, ¬ Disjoint e.toFinset f.toFinset)
    (cover : ∀ e ∈ X, ∃ g ∈ K, e ∈ F g) : X.card ≤ capacity K.card := by
  classical
  let a (g : ℕ) : Fin 14 := if h : g ∈ K then
      Classical.choose (block_contains (F g) (fun {_} he => inside g h he) (close g h)) else 0
  have h (g) (hg : g ∈ K) : F g ⊆ (block (a g)).image edge := by
    simp only [a, dite_eq_left hg]
    exact Classical.choose_spec (block_contains (F g) (fun {_} he => inside g hg he) (close g hg))
  exact (project_cover a h cover).trans ((capacities _).1.trans (capacity_mono Finset.card_image_le))

theorem junk_capacity (C : PEqualNP.CircuitLowerBounds.Circuit) (X : Finset Edge)
    (K : Finset ℕ) (cover : ∀ e ∈ X, ∃ g ∈ K, e ∈ gammaE graph C g)
    (close : ∀ g ∈ K, ∀ e ∈ X ∩ gammaE graph C g, ∀ f ∈ X ∩ gammaE graph C g,
      ¬ Disjoint e.toFinset f.toFinset) : X.card ≤ capacity K.card :=
  intersecting_family (F := fun g => X ∩ gammaE graph C g)
    (fun _ _ _ he => (Finset.mem_filter.mp (Finset.mem_inter.mp he).2).1)
    close (fun e he => by
      obtain ⟨g,hg,h⟩ := cover e he
      exact ⟨g,hg,Finset.mem_inter.mpr ⟨he,h⟩⟩)

theorem capacity_surplus (k : Nat) : capacity k ≤ k + 11 := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => decide
  | n+5 => simp [capacity]

theorem junk_charge (C : PEqualNP.CircuitLowerBounds.Circuit) (X : Finset Edge) (K : Finset ℕ)
    (cover : ∀ e ∈ X, ∃ g ∈ K, e ∈ gammaE graph C g)
    (close : ∀ g ∈ K, ∀ e ∈ X ∩ gammaE graph C g, ∀ f ∈ X ∩ gammaE graph C g,
      ¬ Disjoint e.toFinset f.toFinset)
    (budget : 11 ≤ 2 * (centreless graph C).card + (orN graph C \ lam graph C).card) :
    X.card ≤ 2 * (centreless graph C).card + K.card + (orN graph C \ lam graph C).card := by
  have h := (junk_capacity C X K cover close).trans (capacity_surplus K.card)
  omega
def mixedWitness : Nat → Finset (Fin 14)
  | 0 => ∅
  | 1 => {8}
  | 2 => {8,10}
  | 3 => {7,8,10}
  | 4 => {8,9,10,12}
  | _ => {5,9,10,11,12}

def starWitness : Nat → Finset (Fin 14)
  | 0 => ∅
  | 1 => {8}
  | 2 => {8,10}
  | 3 => {7,8,10}
  | 4 => {3,8,9,10}
  | 5 => {0,5,7,8,10}
  | 6 => {0,1,5,7,8,10}
  | _ => {0,1,3,5,7,8,10}

theorem mixed_attained (k : Nat) :
    (mixedWitness k).card ≤ k ∧ ((mixedWitness k).biUnion block).card = capacity k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => decide
  | n+5 =>
    have h : (mixedWitness 5).card = 5 ∧ ((mixedWitness 5).biUnion block).card = 16 := by decide
    exact ⟨h.1.le.trans (by omega), h.2⟩

theorem stars_attained (k : Nat) : (starWitness k).card ≤ k ∧
    (∀ a ∈ starWitness k, a.val < 11) ∧ ((starWitness k).biUnion block).card = starCapacity k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n+7 =>
    have h : (starWitness 7).card = 7 ∧ (∀ a ∈ starWitness 7, a.val < 11) ∧
        ((starWitness 7).biUnion block).card = 16 := by decide
    exact ⟨h.1.le.trans (by omega), h.2⟩

theorem optimal_private_edges : ∀ i : Fin 16,
    ({5,9,10,11,12} : Finset (Fin 14)).filter (fun a => i ∈ block a) =
      if i = 11 then {5,9}
      else if i ∈ block 5 then {5}
      else if i ∈ block 9 then {9}
      else if i ∈ block 10 then {10}
      else if i ∈ block 11 then {11} else {12} := by decide +kernel

end PEqualNP.Research.Residual6752

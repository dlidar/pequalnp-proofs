import ExactPool
namespace PEqualNP.Research.Example4697
open Finset PEqualNP.Research.Pool4697 PEqualNP.EdgeOwnership
set_option maxHeartbeats 4000000
abbrev V := Fin 24
def G := edgeGraph 24 [(0, 1),(0, 12),(0, 23),(1, 2),(1, 8),(2, 3),(2, 19),(3, 4),(3, 15),(4, 5),(4, 11),(5, 6),(5, 22),(6, 7),(6, 18),(7, 8),(7, 14),(8, 9),(9, 10),(9, 21),(10, 11),(10, 17),(11, 12),(12, 13),(13, 14),(13, 20),(14, 15),(15, 16),(16, 17),(16, 23),(17, 18),(18, 19),(19, 20),(20, 21),(21, 22),(22, 23)]
instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)
def verts (s : Nat) : Finset V := univ.filter (fun i => s.testBit i.val)
def Free (I : Finset V) := ∀ a∈I,∀ b∈I, ¬G.Adj a b
def Cap (S : Finset V) (k : Nat) := ∀ I ⊆ S, Free I → I.card ≤ k
def clique (S : Finset V) := ∀ a∈S,∀ b∈S,a≠b → G.Adj a b
instance (S : Finset V) : Decidable (clique S) := by unfold clique; infer_instance
theorem clique_cap {S} (c : clique S) : Cap S 1 := by
  intro I sub f
  apply card_le_one.mpr
  intro a ha b hb
  by_contra ne
  exact f a ha b hb (c a (sub ha) b (sub hb) ne)
theorem clique_list (sets : List (Finset V)) (ok : ∀ S ∈ sets,clique S) :
    Cap (sets.foldr (· ∪ ·) ∅) sets.length := by
  induction sets with
  | nil => intro I sub f; simpa using card_le_card sub
  | cons A tail ih =>
    intro I sub f
    let X := I ∩ A
    let Y := I \ A
    have small := clique_cap (ok A (by simp)) X inter_subset_right (fun a ha b hb => f a (mem_inter.mp ha).1 b (mem_inter.mp hb).1)
    have ys : Y ⊆ tail.foldr (· ∪ ·) ∅ := by
      intro v hv
      have h := mem_sdiff.mp hv
      exact (mem_union.mp (sub h.1)).resolve_left h.2
    have bound := ih (fun S h => ok S (by simp [h])) Y ys (fun a ha b hb => f a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1)
    have eq : X ∪ Y = I := by ext v; simp [X,Y]
    have count := card_union_le X Y
    rw [eq] at count
    simp only [List.length_cons];omega
theorem leaf (s k : Nat) (blocks : List (Finset V)) (ok : ∀ S ∈ blocks,clique S)
    (sub : verts s ⊆ blocks.foldr (· ∪ ·) ∅) (le : blocks.length ≤ k) : Cap (verts s) k :=
  fun I h f => (clique_list blocks ok I (h.trans sub) f).trans le
theorem fork (s v t u k : Nat) (a : V) (del : (verts s).erase a ⊆ verts t)
    (nbr : ∀ z ∈ (verts s).erase a, ¬G.Adj a z → z∈verts u)
    (x : Cap (verts t) (k+1)) (y : Cap (verts u) k) : Cap (verts s) (k+1) := by
  intro I sub f
  by_cases ha : a ∈ I
  · have h : I.erase a ⊆ verts u := by
      intro z hz
      have e := mem_erase.mp hz
      exact nbr z (mem_erase.mpr ⟨e.1,sub e.2⟩) (f a ha z e.2)
    have b := y _ h (fun i hi j hj => f i (mem_of_mem_erase hi) j (mem_of_mem_erase hj))
    rw [card_erase_of_mem ha] at b
    omega
  · apply x I _ f
    intro z hz
    exact del (mem_erase.mpr ⟨fun e => ha (e ▸ hz),sub hz⟩)
private theorem node16777130_10 : Cap (verts 16777130) 10 := by
  exact leaf _ _ [{1,8},{3,15},{5,22},{7,14},{23,16},{9,21},{10,11},{12,13},{17,18},{19,20}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node16514826_9 : Cap (verts 16514826) 9 := by
  exact leaf _ _ [{1,8},{3,15},{14,13},{12,11},{19,20},{9,10},{17,16},{21,22},{23}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node16777194_10 : Cap (verts 16777194) 10 := by
  exact fork 16777194 0 16777130 16514826 9 6 (by decide +kernel) (by decide +kernel) node16777130_10 node16514826_9
private theorem node16775106_9 : Cap (verts 16775106) 9 := by
  exact leaf _ _ [{1,8},{12,13},{6,7},{14,15},{9,10},{16,17},{18,19},{20,21},{22,23}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node16777210_10 : Cap (verts 16777210) 10 := by
  exact fork 16777210 0 16777194 16775106 9 4 (by decide +kernel) (by decide +kernel) node16777194_10 node16775106_9
private theorem node16252880_9 : Cap (verts 16252880) 9 := by
  exact leaf _ _ [{4,11},{12,13},{20,21},{22,23},{6,18},{7,8},{9,10},{14,15},{16,17}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node12058496_8 : Cap (verts 12058496) 8 := by
  exact leaf _ _ [{18,17},{23,16},{15,14},{7,8},{9,10},{11,12},{13,20},{21}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node16252912_9 : Cap (verts 16252912) 9 := by
  exact fork 16252912 0 16252880 12058496 8 5 (by decide +kernel) (by decide +kernel) node16252880_9 node12058496_8
private theorem node16777214_10 : Cap (verts 16777214) 10 := by
  exact fork 16777214 0 16777210 16252912 9 2 (by decide +kernel) (by decide +kernel) node16777210_10 node16252912_9
private theorem node8384468_9 : Cap (verts 8384468) 9 := by
  exact leaf _ _ [{2,19},{4,11},{22,21},{20,13},{6,18},{7,8},{9,10},{14,15},{16,17}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node4190084_8 : Cap (verts 4190084) 8 := by
  exact leaf _ _ [{2,19},{11,10},{18,17},{16,15},{7,8},{9,21},{14,13},{20}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node8384500_9 : Cap (verts 8384500) 9 := by
  exact fork 8384500 0 8384468 4190084 8 5 (by decide +kernel) (by decide +kernel) node8384468_9 node4190084_8
private theorem node8351712_8 : Cap (verts 8351712) 8 := by
  exact leaf _ _ [{11,10},{16,17},{5,22},{6,18},{19,20},{13,14},{7,8},{9,21}] (by intro S hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem node8384508_9 : Cap (verts 8384508) 9 := by
  exact fork 8384508 0 8384500 8351712 8 3 (by decide +kernel) (by decide +kernel) node8384500_9 node8351712_8
private theorem node16777215_10 : Cap (verts 16777215) 10 := by
  exact fork 16777215 0 16777214 8384508 9 0 (by decide +kernel) (by decide +kernel) node16777214_10 node8384508_9
theorem independent_bound (I : Finset V) (free : Free I) : I.card ≤ 10 := by
  have eq : verts 16777215 = univ := by decide +kernel
  exact node16777215_10 I (eq.symm ▸ subset_univ I) free
theorem cover_bound (K : Finset V) (cov : G.IsVertexCover ↑K) : 14 ≤ K.card := by
  have b := independent_bound (univ \ K) (by
    intro a ha b hb edge
    rcases cov edge with h|h
    · exact (mem_sdiff.mp ha).2 h
    · exact (mem_sdiff.mp hb).2 h)
  rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin] at b
  omega
def witness := verts 5592925
theorem cover_witness : G.IsVertexCover ↑witness := by
  change ∀ ⦃a b : V⦄, G.Adj a b → a∈witness ∨ b∈witness
  decide +kernel
theorem witness_size : witness.card = 14 := by decide +kernel
theorem edge_count : G.edgeSet.ncard = 36 := by
  rw [Set.ncard_eq_toFinset_card']; change G.edgeFinset.card=36;decide +kernel
theorem thin : Thin G := by unfold Thin;decide +kernel
theorem cubic : ∀ a : V,G.degree a=3 := by decide +kernel
theorem exact_pool (s : Nat) : (∃ B m X Y,Represents G B m X Y ∧ B.length+2*m ≤ s) ↔ 50 ≤ s := by
  rw [exact_budget G thin]
  constructor
  · rintro ⟨K,cov,b⟩
    have h := cover_bound K cov
    rw [edge_count] at b;omega
  · intro h
    exact ⟨witness,cover_witness,by rwa [edge_count,witness_size]⟩
end PEqualNP.Research.Example4697

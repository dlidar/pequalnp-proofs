import Pool
namespace PEqualNP.Research.Pool4697
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Thin := ∀ a b : V,a ≠ b → (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1

theorem orient [Nonempty V] (thin : Thin G) (X Y : Finset V)
    (cross : ∀ a ∈ X,∀ b ∈ Y,G.Adj a b) :
    ∃ c : V,∃ S : Finset V, (S=∅ ∨ S=X ∨ S=Y) ∧ S ⊆ G.neighborFinset c ∧
      ∀ a ∈ X,∀ b ∈ Y,(a=c ∧ b∈S) ∨ (b=c ∧ a∈S) := by
  classical
  by_cases ex : X.Nonempty
  · obtain ⟨a,ha⟩ := ex
    by_cases small : X.card ≤ 1
    · exact ⟨a,Y,Or.inr (Or.inr rfl),fun b hb => by simpa using cross a ha b hb,
        fun x hx y hy => Or.inl ⟨card_le_one.mp small _ hx _ ha,hy⟩⟩
    · obtain ⟨x,hx,z,hz,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge small)
      have sub : Y ⊆ G.neighborFinset x ∩ G.neighborFinset z := fun b hb =>
        mem_inter.mpr ⟨by simpa using cross x hx b hb,by simpa using cross z hz b hb⟩
      have sy := (card_le_card sub).trans (thin x z ne)
      by_cases ey : Y.Nonempty
      · obtain ⟨b,hb⟩ := ey
        exact ⟨b,X,Or.inr (Or.inl rfl),fun x hx => by simpa using (cross x hx b hb).symm,
          fun a ha y hy => Or.inr ⟨card_le_one.mp sy _ hy _ hb,ha⟩⟩
      · exact ⟨a,∅,Or.inl rfl,empty_subset _,fun _ _ y hy => (ey ⟨y,hy⟩).elim⟩
  · exact ⟨Classical.arbitrary V,∅,Or.inl rfl,empty_subset _,fun a ha => (ex ⟨a,ha⟩).elim⟩

theorem charge [Nonempty V] (thin : Thin G) (B : List (Finset V)) (m : Nat)
    (X Y : Fin m → Finset V) (built : Built B)
    (avail : ∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B))
    (correct : ∀ x : V → Bool, (∃ i, (∃ u ∈ X i,x u=true) ∧ ∃ v ∈ Y i,x v=true) ↔
      ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ T : Finset V,G.IsVertexCover ↑T ∧ T.card ≤ m ∧ G.edgeSet.ncard ≤ B.length+m := by
  classical
  obtain ⟨cross,complete⟩ := pair_edges correct
  choose c S source inside hit using fun i => orient G thin (X i) (Y i) (cross i)
  obtain ⟨n,W,raw,gate,find⟩ := layout B built
  have availS (i) : (S i).card ≤ 1 ∨ S i ∈ B := by
    rcases source i with h|h|h
    · simp [h]
    · rw [h];exact (avail i).1
    · rw [h];exact (avail i).2
  choose arm valid val using fun i => find (S i) (availS i)
  let T := univ.image c
  let arms (v : V) := (univ.filter fun i => c i=v).image arm
  let leaves (v : V) := (arms v).biUnion W
  have bound : ∑ v ∈ T, (leaves v).card ≤ m+B.length :=
    StarNetworks.star_leaf_count n B.length m W raw gate (fun v => G.neighborFinset v) thin c arm valid (fun i => val i ▸ inside i)
  have occurs (i) {v} (hv : v ∈ S i) : v ∈ leaves (c i) :=
    mem_biUnion.mpr ⟨arm i,mem_image.mpr ⟨i,by simp,rfl⟩,by rwa [val]⟩
  have pairs (a b) (ab : G.Adj a b) : ∃ i,(a=c i ∧ b∈leaves (c i)) ∨ (b=c i ∧ a∈leaves (c i)) := by
    obtain ⟨i,h⟩ := complete a b ab
    refine ⟨i,?_⟩
    rcases h with h|h
    · rcases hit i a h.1 b h.2 with ⟨e,x⟩|⟨e,x⟩
      · exact Or.inl ⟨e,occurs i x⟩
      · exact Or.inr ⟨e,occurs i x⟩
    · rcases hit i b h.1 a h.2 with ⟨e,x⟩|⟨e,x⟩
      · exact Or.inr ⟨e,occurs i x⟩
      · exact Or.inl ⟨e,occurs i x⟩
  have cm (i) : c i ∈ T := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have tc : T.card ≤ m := card_image_le.trans (by simp)
  refine ⟨T,?_,tc,?_⟩
  · intro a b ab
    obtain ⟨i,h|h⟩ := pairs _ _ ab
    · exact Or.inl (h.1 ▸ cm i)
    · exact Or.inr (h.1 ▸ cm i)
  · let group (v : V) := (leaves v).image (fun b => s(v,b))
    have sub : G.edgeFinset ⊆ T.biUnion group := by
      intro e
      induction e using Sym2.ind with
      | h a b =>
        intro he
        obtain ⟨i,h|h⟩ := pairs a b (by simpa using he)
        · exact mem_biUnion.mpr ⟨c i,cm i,mem_image.mpr ⟨b,h.2,by rw [h.1]⟩⟩
        · exact mem_biUnion.mpr ⟨c i,cm i,mem_image.mpr ⟨a,h.2,by rw [h.1];exact Sym2.eq_swap⟩⟩
    have count := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (fun v (_ : v ∈ T) => (card_image_le : (group v).card ≤ (leaves v).card))))
    have e := count.trans bound
    have same : G.edgeSet.ncard = G.edgeFinset.card := by rw [Set.ncard_eq_toFinset_card'];rfl
    omega
end PEqualNP.Research.Pool4697

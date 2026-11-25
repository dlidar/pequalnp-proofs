import PEqualNP.Research.CoreCover2962.CoverCuts
import Mathlib.Combinatorics.Hall.Basic

/-! Match a minimum cover to distinct outside neighbors. Count exactly the
matching edges a residual cover misses, with credits for double hits and for
vertices off the matching. -/
namespace PEqualNP.Research.CoreCoverCuts
open Finset PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (V n)} [DecidableRel G.Adj]

theorem exchange_covers {T A : Finset (V n)} (t : G.IsVertexCover (T : Set (V n)))
    (indep : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) :
    G.IsVertexCover (((T \ A) ∪ (neighbors G A \ T) : Finset _) : Set (V n)) := by
  intro u v adj
  change u ∈ _ ∨ v ∈ _
  simp only [Finset.mem_coe,mem_union,mem_sdiff, mem_neighbors]
  have extn {u v} (hu : u ∈ A) (h : G.Adj u v) :
      (v ∈ T ∧ v ∉ A) ∨ ((∃ w ∈ A, G.Adj w v) ∧ v ∉ T) := by
    by_cases hv : v ∈ T
    · exact Or.inl ⟨hv,fun va => indep _ hu _ va h⟩
    · exact Or.inr ⟨⟨u,hu,h⟩,hv⟩
  rcases t adj with ht | ht
  · by_cases m : u ∈ A
    · exact Or.inr (extn m adj)
    · exact Or.inl (Or.inl ⟨ht,m⟩)
  · by_cases m : v ∈ A
    · exact Or.inl (extn m adj.symm)
    · exact Or.inr (Or.inl ⟨ht,m⟩)

theorem independent_expands {T A : Finset (V n)} (t : IsMinCover G T) (atT : A ⊆ T)
    (indep : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) :
    A.card ≤ (neighbors G A \ T).card := by
  have h := t.2 _ (exchange_covers t.1 indep)
  have z := Finset.card_union_le (T \ A) (neighbors G A \ T)
  rw [card_sdiff_of_subset atT] at z
  have := Finset.card_le_card atT
  omega

theorem cover_hall {L T A : Finset (V n)} (p : Parts G L) (t : IsMinCover G T) (atT : A ⊆ T) :
    A.card ≤ (neighbors G A \ T).card := by
  let X := A ∩ L
  let Y := A \ L
  have ax : X ⊆ A := inter_subset_left
  have ay : Y ⊆ A := sdiff_subset
  have hx := independent_expands t (ax.trans atT) (by
    intro u hu v hv adj
    exact (p u v adj).mp (mem_inter.mp hu).2 (mem_inter.mp hv).2)
  have hy := independent_expands t (ay.trans atT) (by
    intro u hu v hv adj
    exact (mem_sdiff.mp hu).2 ((p u v adj).mpr (mem_sdiff.mp hv).2))
  have dis : Disjoint (neighbors G X \ T) (neighbors G Y \ T) := by
    apply disjoint_left.mpr
    intro v vx vy
    obtain ⟨x,m,h⟩ := mem_neighbors.mp (mem_sdiff.mp vx).1
    obtain ⟨y,my,hy'⟩ := mem_neighbors.mp (mem_sdiff.mp vy).1
    exact (mem_sdiff.mp my).2 ((p _ _ hy').mpr ((p _ _ h).mp (mem_inter.mp m).2))
  have mono {B : Finset (V n)} (sub : B ⊆ A) : neighbors G B \ T ⊆ neighbors G A \ T := by
    intro v hv
    obtain ⟨w,hw,adj⟩ := mem_neighbors.mp (mem_sdiff.mp hv).1
    exact mem_sdiff.mpr ⟨mem_neighbors.mpr ⟨w,sub hw,adj⟩,(mem_sdiff.mp hv).2⟩
  have total := card_le_card (union_subset (mono ax) (mono ay))
  rw [card_union_of_disjoint dis] at total
  have add : X.card + Y.card = A.card := by
    simpa [X,Y,add_comm] using Finset.card_sdiff_add_card_inter A L
  omega

/-- Partners saturate the given optimum. The edges are pairwise disjoint. -/
theorem partners_exist {L T : Finset (V n)} (p : Parts G L) (t : IsMinCover G T) :
    ∃ f : T → V n, Function.Injective f ∧ ∀ x, G.Adj x.val (f x) ∧ f x ∉ T := by
  let opts := fun (u : T) => neighbors G {u.val} \ T
  have test : ∀ s : Finset T, s.card ≤ (s.biUnion opts).card := by
    intro s
    let A := s.image Subtype.val
    have aT : A ⊆ T := fun v hv => by
      obtain ⟨u,_,rfl⟩ := mem_image.mp hv
      exact u.property
    have c := cover_hall p t aT
    have eq : s.biUnion opts = neighbors G A \ T := by
      ext v
      constructor
      · intro hv
        obtain ⟨u,hu,vv⟩ := mem_biUnion.mp hv
        obtain ⟨w,hw,h⟩ := mem_neighbors.mp (mem_sdiff.mp vv).1
        exact mem_sdiff.mpr ⟨mem_neighbors.mpr ⟨u.val,mem_image_of_mem _ hu,mem_singleton.mp hw ▸ h⟩,
          (mem_sdiff.mp vv).2⟩
      · intro hv
        obtain ⟨w,m,adj⟩ := mem_neighbors.mp (mem_sdiff.mp hv).1
        obtain ⟨u,hu,rfl⟩ := mem_image.mp m
        exact mem_biUnion.mpr ⟨u,hu,mem_sdiff.mpr ⟨mem_neighbors.mpr ⟨u.val,mem_singleton_self _,adj⟩,
          (mem_sdiff.mp hv).2⟩⟩
    rw [eq]
    rwa [show A.card = s.card from card_image_of_injective _ Subtype.val_injective] at c
  obtain ⟨f,inj,e⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective opts).mp test
  refine ⟨f,inj,fun u => ?_⟩
  obtain ⟨w,hw,adj⟩ := mem_neighbors.mp (mem_sdiff.mp (e u)).1
  exact ⟨mem_singleton.mp hw ▸ adj,(mem_sdiff.mp (e u)).2⟩

end PEqualNP.Research.CoreCoverCuts

namespace PEqualNP.Research.CoreCoverCuts
open Finset PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {T : Finset (V n)}

def leftHits (K : Finset (V n)) : Finset T := univ.filter fun u => u.val ∈ K
def rightHits (f : T → V n) (K : Finset (V n)) := univ.filter fun u => f u ∈ K
def missed (f : T → V n) (K : Finset (V n)) := univ \ (leftHits K ∪ rightHits f K)
def twice (f : T → V n) (K : Finset (V n)) := leftHits K ∩ rightHits f K
def offMatching (f : T → V n) (K : Finset (V n)) := K \ (T ∪ univ.image f)

theorem exact_matching_loss (f : T → V n) (inj : Function.Injective f) (out : ∀ u, f u ∉ T)
    (K : Finset (V n)) :
    T.card + (twice f K).card + (offMatching f K).card = K.card + (missed f K).card := by
  classical
  let a := leftHits (T := T) K
  let b := rightHits f K
  have imA : a.image Subtype.val = K ∩ T := by
    ext v
    constructor
    · rintro hv
      obtain ⟨u,m,rfl⟩ := mem_image.mp hv
      exact mem_inter.mpr ⟨(mem_filter.mp m).2,u.property⟩
    · intro hv
      obtain ⟨hK,hT⟩ := mem_inter.mp hv
      exact mem_image.mpr ⟨⟨v,hT⟩,mem_filter.mpr ⟨mem_univ _,hK⟩,rfl⟩
  have imB : b.image f = K ∩ univ.image f := by
    ext v
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := mem_image.mp h
      exact mem_inter.mpr ⟨(mem_filter.mp hu).2,mem_image_of_mem _ (mem_univ u)⟩
    · intro h
      obtain ⟨u,_,rfl⟩ := mem_image.mp (mem_inter.mp h).2
      exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,(mem_inter.mp h).1⟩,rfl⟩
  have ca : (K ∩ T).card = a.card := by
    rw [← imA,card_image_of_injective _ Subtype.val_injective]
  have cb : (K ∩ univ.image f).card = b.card := by rw [← imB,card_image_of_injective _ inj]
  have dis : Disjoint (K ∩ T) (K ∩ univ.image f) := by
    apply disjoint_left.mpr
    intro v hv hv'
    obtain ⟨u,_,rfl⟩ := mem_image.mp (mem_inter.mp hv').2
    exact out u (mem_inter.mp hv).2
  have part := card_sdiff_add_card_inter K (T ∪ univ.image f)
  rw [inter_union_distrib_left,card_union_of_disjoint dis,ca,cb] at part
  have incl := card_union_add_card_inter a b
  have rest := card_sdiff_add_card_inter (univ : Finset T) (a ∪ b)
  simp only [univ_inter,card_univ,Fintype.card_coe] at rest
  change T.card + (a ∩ b).card + (K \ (T ∪ univ.image f)).card =
    K.card + (univ \ (a ∪ b)).card
  omega

theorem missed_deleted {G : SimpleGraph (V n)} {D : Finset (Sym2 (V n))}
    {f : T → V n} (adj : ∀ u, G.Adj u.val (f u)) {K : Finset (V n)}
    (k : (G.deleteEdges (D : Set _)).IsVertexCover (K : Set _)) {u : T}
    (m : u ∈ missed f K) : s(u.val, f u) ∈ D := by
  have hm := (mem_sdiff.mp m).2
  by_contra notD
  have hh : (G.deleteEdges (D : Set _)).Adj u.val (f u) := SimpleGraph.deleteEdges_adj.mpr ⟨adj u,notD⟩
  rcases k hh with a | b
  · exact hm (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,a⟩))
  · exact hm (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,b⟩))

theorem matched_budget_iff {H : SimpleGraph (V n)} {K : Finset (V n)} (k : IsMinCover H K)
    (f : T → V n) (inj : Function.Injective f) (out : ∀ u, f u ∉ T) (d budget : Nat) :
    d + T.card ≤ budget + K.card ↔
    ∀ S : Finset (V n), H.IsVertexCover (S : Set _) →
      d + (missed f S).card ≤ budget + (twice f S).card + (offMatching f S).card := by
  constructor
  · intro target S hs
    have h := exact_matching_loss f inj out S
    have low := k.2 S hs
    omega
  · intro test
    have q := test K k.1
    have h := exact_matching_loss f inj out K
    omega

end PEqualNP.Research.CoreCoverCuts

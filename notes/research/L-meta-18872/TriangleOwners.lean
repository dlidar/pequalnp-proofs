import Mathlib
namespace PEqualNP.Research.TripleOwners
open Finset
abbrev Edge := Fin 15
abbrev Triangle := Fin 20
def verts (t : Triangle) : Finset Edge := ([{0,1,5}, {0,2,6}, {0,3,7}, {0,4,8}, {1,2,9}, {1,3,10}, {1,4,11}, {2,3,12}, {2,4,13}, {3,4,14}, {5,6,9}, {5,7,10}, {5,8,11}, {6,7,12}, {6,8,13}, {7,8,14}, {9,10,12}, {9,11,13}, {10,11,14}, {12,13,14}] : List (Finset Edge)).getD t.val ∅
def hitB (s : Finset Edge) := (List.finRange 20).all (fun t => decide (0 < ((verts t) ∩ s).card))
def Hit (s : Finset Edge) := hitB s=true
instance (s : Finset Edge) : Decidable (Hit s) := inferInstanceAs (Decidable (hitB s=true))
theorem hit_spec (s : Finset Edge) : Hit s ↔ ∀ t : Triangle,∃ i∈verts t,i∈s := by
  simp [Hit,hitB,List.all_eq_true,card_pos,Finset.Nonempty]
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
theorem no_five : ((univ.powersetCard 5).filter Hit : Finset (Finset Edge))=∅ := by decide +kernel
theorem owner_bound (s : Finset Edge) (h : Hit s) : 6 ≤ s.card := by
  by_contra! low
  obtain ⟨u, su, _, cu⟩ := exists_subsuperset_card_eq (subset_univ s) (show s.card ≤ 5 by omega)
    (show 5 ≤ (univ : Finset Edge).card by decide)
  have hu : Hit u := (hit_spec _).mpr (fun t => by
    obtain ⟨i,hi,hj⟩ := (hit_spec _).mp h t
    exact ⟨i,hi,su hj⟩)
  have mem : u ∈ ((univ.powersetCard 5).filter Hit : Finset (Finset Edge)) :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,cu⟩,hu⟩
  simp [no_five] at mem
theorem six_owners : Hit ({0,1,5,12,13,14} : Finset Edge) := by decide +kernel
def forms (i j k : Edge) (t : Triangle) : Prop := ({i,j,k} : Finset Edge) = verts t
instance (i j k : Edge) (t : Triangle) : Decidable (forms i j k t) := inferInstanceAs (Decidable (({i,j,k} : Finset Edge) = verts t))
def third (i j : Edge) : Nat :=
  ([15, 5, 6, 7, 8, 1, 2, 3, 4, 15, 15, 15, 15, 15, 15, 5, 15, 9, 10, 11, 0, 15, 15, 15, 2, 3, 4, 15, 15, 15, 6, 9, 15, 12, 13, 15, 0, 15, 15, 1, 15, 15, 3, 4, 15, 7, 10, 12, 15, 14, 15, 15, 0, 15, 15, 1, 15, 2, 15, 4, 8, 11, 13, 14, 15, 15, 15, 15, 0, 15, 15, 1, 15, 2, 3, 1, 0, 15, 15, 15, 15, 9, 10, 11, 6, 7, 8, 15, 15, 15, 2, 15, 0, 15, 15, 9, 15, 12, 13, 5, 15, 15, 7, 8, 15, 3, 15, 15, 0, 15, 10, 12, 15, 14, 15, 5, 15, 6, 15, 8, 4, 15, 15, 15, 0, 11, 13, 14, 15, 15, 15, 5, 15, 6, 7, 15, 2, 1, 15, 15, 6, 5, 15, 15, 15, 12, 13, 10, 11, 15, 15, 3, 15, 1, 15, 7, 15, 5, 15, 12, 15, 14, 9, 15, 11, 15, 4, 15, 15, 1, 8, 15, 15, 5, 13, 14, 15, 15, 9, 10, 15, 15, 3, 2, 15, 15, 7, 6, 15, 10, 9, 15, 15, 14, 13, 15, 15, 4, 15, 2, 15, 8, 15, 6, 11, 15, 9, 14, 15, 12, 15, 15, 15, 4, 3, 15, 15, 8, 7, 15, 11, 10, 13, 12, 15] : List Nat).getD (15*i.val+j.val) 15
theorem completes : ∀ t : Triangle, ∀ i∈verts t, ∀ j∈verts t,∀ k∈verts t,
    forms i j k t → third i j=k.val ∧ third j k=i.val ∧ third k i=j.val := by decide +kernel
theorem unique_edges {i j k t} (h : forms i j k t) :
    third i j=k.val ∧ third j k=i.val ∧ third k i=j.val := by
  apply completes t i _ j _ k _ h <;> rw [← h] <;> simp
theorem distinct_triangles : Function.Injective verts := by
  intro a b
  have test : ∀ t u : Triangle, verts t=verts u → t=u := by decide +kernel
  exact test a b
end PEqualNP.Research.TripleOwners

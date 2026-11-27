import CoreClass

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

namespace FourRowCore
open Finset

def masks : List (Fin 16) := [3,5,6,7,9,10,11,12,13,14,15]

theorem masks_exact : masks.toFinset = big := by decide +kernel

def search (s : Finset (Fin 16)) : List (Fin 16) → List (Finset (Fin 16))
  | [] => if good s then [s] else []
  | v :: vs =>
    search s vs ++ (if ∀ w ∈ s, v = w ∨ (rows v ∩ rows w).card ≤ 1
      then search (insert v s) vs else [])

theorem in_search {L : Finset (Fin 16)} (ok : good L) (vs : List (Fin 16))
    (s : Finset (Fin 16)) (sub : s ⊆ L) (cover : L ⊆ s ∪ vs.toFinset) :
    L ∈ search s vs := by
  induction vs generalizing s with
  | nil =>
    have eq := Finset.Subset.antisymm sub (by simpa using cover)
    subst s
    rw [search,if_pos ok]
    simp
  | cons v vs ih =>
    simp only [search,List.mem_append]
    by_cases mem : v ∈ L
    · right
      have hp := ok.1
      rw [if_pos (fun w hw => hp v mem w (sub hw))]
      apply ih (insert v s) (Finset.insert_subset mem sub)
      intro a ha
      rcases mem_union.mp (cover ha) with hs | ht
      · exact mem_union_left _ (mem_insert_of_mem hs)
      · rcases List.mem_cons.mp (List.mem_toFinset.mp ht) with rfl | ht
        · exact mem_union_left _ (mem_insert_self _ _)
        · exact mem_union_right _ (List.mem_toFinset.mpr ht)
    · left
      apply ih s sub
      intro a ha
      rcases mem_union.mp (cover ha) with hs | ht
      · exact mem_union_left _ hs
      · rcases List.mem_cons.mp (List.mem_toFinset.mp ht) with rfl | ht
        · exact (mem ha).elim
        · exact mem_union_right _ (List.mem_toFinset.mpr ht)

theorem search_sound (vs : List (Fin 16)) (s L : Finset (Fin 16))
    (mem : L ∈ search s vs) : good L ∧ L ⊆ s ∪ vs.toFinset := by
  induction vs generalizing s with
  | nil =>
    by_cases ok : good s
    · rw [search,if_pos ok] at mem
      have eq : L = s := List.mem_singleton.mp mem
      subst L
      simpa using And.intro ok (Finset.Subset.refl s)
    · simp [search,ok] at mem
  | cons v vs ih =>
    simp only [search,List.mem_append] at mem
    rcases mem with h | h
    · obtain ⟨ok,sub⟩ := ih s h
      refine ⟨ok,fun a ha => ?_⟩
      rcases mem_union.mp (sub ha) with hs | hv
      · exact mem_union_left _ hs
      · exact mem_union_right _ (by simp [List.mem_toFinset.mp hv])
    · split at h
      next =>
        obtain ⟨ok,sub⟩ := ih (insert v s) h
        refine ⟨ok,fun a ha => ?_⟩
        rcases mem_union.mp (sub ha) with hs | hv
        · rcases mem_insert.mp hs with rfl | hs
          · exact mem_union_right _ (by simp)
          · exact mem_union_left _ hs
        · exact mem_union_right _ (by simp [List.mem_toFinset.mp hv])
      next => simp at h

theorem enumerates : legal = (search ∅ masks).toFinset := by
  ext L
  constructor
  · intro mem
    obtain ⟨sub,ok⟩ := mem_filter.mp mem
    apply List.mem_toFinset.mpr
    apply in_search ok masks ∅ (empty_subset _)
    simpa [masks_exact] using mem_powerset.mp sub
  · intro mem
    obtain ⟨ok,sub⟩ := search_sound masks ∅ L (List.mem_toFinset.mp mem)
    exact mem_filter.mpr ⟨mem_powerset.mpr (by simpa [masks_exact] using sub),ok⟩

def fourteen : Finset (Finset (Fin 16)) := {
  {3,5,9,14},
  {3,5,10,12},
  {3,6,9,12},
  {3,6,10,13},
  {5,6,9,10},
  {5,6,11,12},
  {7,9,10,12},
  {3,5,6,9,10},
  {3,5,6,9,12},
  {3,5,6,10,12},
  {3,5,9,10,12},
  {3,6,9,10,12},
  {5,6,9,10,12},
  {3,5,6,9,10,12}}

theorem exact_census : legal = fourteen := by
  rw [enumerates]
  decide +kernel

theorem fourteen_distinct : fourteen.card = 14 := by decide +kernel

end FourRowCore

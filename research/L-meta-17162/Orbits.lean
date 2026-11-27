import Census
namespace FourRowCore
open Finset

def relabel (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 16)) :=
  L.image (fun v => pack ((rows v).image π))

def representatives : Finset (Finset (Fin 16)) :=
  {{3,5,10,12}, {3,5,6,9,10}, {3,5,6,9,10,12}, {3,5,9,14}}

theorem four_types {L : Finset (Fin 16)} (h : L ∈ legal) :
    ∃ π : Equiv.Perm (Fin 4), relabel π L ∈ representatives := by
  rw [exact_census] at h
  simp only [fourteen, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(Equiv.refl (Fin 4)),by decide +kernel⟩
  · exact ⟨(Equiv.refl (Fin 4)),by decide +kernel⟩
  · exact ⟨((Equiv.refl (Fin 4)).trans (Equiv.swap (2 : Fin 4) 3)),by decide +kernel⟩
  · exact ⟨((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 1)),by decide +kernel⟩
  · exact ⟨(((Equiv.refl (Fin 4)).trans (Equiv.swap (1 : Fin 4) 3)).trans (Equiv.swap (2 : Fin 4) 1)),by decide +kernel⟩
  · exact ⟨(((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 1)).trans (Equiv.swap (0 : Fin 4) 2)),by decide +kernel⟩
  · exact ⟨((((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 1)).trans (Equiv.swap (0 : Fin 4) 2)).trans (Equiv.swap (0 : Fin 4) 3)),by decide +kernel⟩
  · exact ⟨(Equiv.refl (Fin 4)),by decide +kernel⟩
  · exact ⟨((Equiv.refl (Fin 4)).trans (Equiv.swap (1 : Fin 4) 2)),by decide +kernel⟩
  · exact ⟨(((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 2)).trans (Equiv.swap (1 : Fin 4) 0)),by decide +kernel⟩
  · exact ⟨(((Equiv.refl (Fin 4)).trans (Equiv.swap (1 : Fin 4) 2)).trans (Equiv.swap (1 : Fin 4) 3)),by decide +kernel⟩
  · exact ⟨((((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 2)).trans (Equiv.swap (1 : Fin 4) 0)).trans (Equiv.swap (1 : Fin 4) 3)),by decide +kernel⟩
  · exact ⟨(((Equiv.refl (Fin 4)).trans (Equiv.swap (0 : Fin 4) 2)).trans (Equiv.swap (1 : Fin 4) 3)),by decide +kernel⟩
  · exact ⟨(Equiv.refl (Fin 4)),by decide +kernel⟩

theorem classification {m : ℕ} (E : Finset (Fin 4 × Fin m))
    (wide : ∀ j, 2 ≤ (column E j).card)
    (dense : ∀ i : Fin 4, 2 ≤ (univ.filter (fun j : Fin m => (i,j) ∈ E)).card)
    (c4 : ∀ i k : Fin 4, ∀ j l : Fin m, i≠k → j≠l →
      ¬((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) :
    Function.Injective (encoded E) ∧ ∃ π : Equiv.Perm (Fin 4), relabel π (family E) ∈ representatives :=
  ⟨distinct_codes E wide c4, four_types (family_legal E wide dense c4)⟩
end FourRowCore

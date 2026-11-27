import Mathlib

namespace FourRowCore
open Finset

def rows (v : Fin 16) : Finset (Fin 4) := univ.filter fun i => v.val.testBit i.val

def pack (s : Finset (Fin 4)) : Fin 16 := Fin.ofNat 16 (∑ i ∈ s, 2^i.val)

theorem rows_pack : ∀ s : Finset (Fin 4), rows (pack s) = s := by decide +kernel

def big : Finset (Fin 16) := univ.filter fun v => 2 ≤ (rows v).card

def leftCount (L : Finset (Fin 16)) (i : Fin 4) := (L.filter fun v => i ∈ rows v).card

abbrev good (L : Finset (Fin 16)) : Prop :=
  (∀ v ∈ L, ∀ w ∈ L, v = w ∨ (rows v ∩ rows w).card ≤ 1) ∧
    (∀ i : Fin 4, 2 ≤ leftCount L i)

def legal : Finset (Finset (Fin 16)) := big.powerset.filter fun L => good L

variable {m : ℕ}
def column (E : Finset (Fin 4 × Fin m)) (j : Fin m) : Finset (Fin 4) :=
  univ.filter (fun i => (i,j) ∈ E)

def encoded (E : Finset (Fin 4 × Fin m)) (j : Fin m) := pack (column E j)

def family (E : Finset (Fin 4 × Fin m)) := univ.image (encoded E)

theorem distinct_codes (E : Finset (Fin 4 × Fin m))
    (wide : ∀ j, 2 ≤ (column E j).card)
    (c4 : ∀ i k : Fin 4, ∀ j l : Fin m, i≠k → j≠l →
      ¬((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) :
    Function.Injective (encoded E) := by
  intro j l eq
  by_contra diff
  have same : column E j = column E l := by
    simpa only [encoded,rows_pack] using congrArg rows eq
  obtain ⟨i,hi,k,hk,ik⟩ := Finset.one_lt_card.mp (wide j)
  have hi' := same ▸ hi
  have hk' := same ▸ hk
  exact c4 i k j l ik diff ⟨(mem_filter.mp hi).2,(mem_filter.mp hi').2,
    (mem_filter.mp hk).2,(mem_filter.mp hk').2⟩

theorem family_legal (E : Finset (Fin 4 × Fin m))
    (wide : ∀ j, 2 ≤ (column E j).card)
    (dense : ∀ i : Fin 4, 2 ≤ (univ.filter (fun j : Fin m => (i,j) ∈ E)).card)
    (c4 : ∀ i k : Fin 4, ∀ j l : Fin m, i≠k → j≠l →
      ¬((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) : family E ∈ legal := by
  have inj := distinct_codes E wide c4
  rw [legal,mem_filter,mem_powerset]
  constructor
  · intro v hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hv
    simpa [big,encoded,rows_pack] using wide j
  · constructor
    · intro v hv w hw
      obtain ⟨j,_,rfl⟩ := mem_image.mp hv
      obtain ⟨l,_,rfl⟩ := mem_image.mp hw
      by_cases eq : j=l
      · exact Or.inl (congrArg _ eq)
      · right; simp only [encoded,rows_pack]
        by_contra! h
        obtain ⟨i,hi,k,hk,ik⟩ := Finset.one_lt_card.mp h
        rcases mem_inter.mp hi with ⟨hi,hj⟩
        rcases mem_inter.mp hk with ⟨hk,hl⟩
        exact c4 i k j l ik eq ⟨(mem_filter.mp hi).2,(mem_filter.mp hj).2,
          (mem_filter.mp hk).2,(mem_filter.mp hl).2⟩
    · intro i
      have same : ((univ.filter fun j : Fin m => (i,j) ∈ E).image (encoded E)) =
          (family E).filter (fun v => i ∈ rows v) := by
        ext v
        simp only [mem_image,mem_filter,mem_univ,true_and,family]
        constructor
        · rintro ⟨j,h,rfl⟩
          refine ⟨⟨j,rfl⟩,?_⟩
          simpa [encoded,rows_pack,column] using h
        · rintro ⟨⟨j,rfl⟩,h⟩
          exact ⟨j,by simpa [encoded,rows_pack,column] using h,rfl⟩
      unfold leftCount
      rw [←same, card_image_of_injective _ inj]
      exact dense i

end FourRowCore

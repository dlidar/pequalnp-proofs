import PEqualNP.Research.FlagSamples

namespace PEqualNP.Research.SampleCount
attribute [local instance] Classical.propDecidable
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.FlagSamples PEqualNP.Research.NecessarySamples

theorem flag_has_edge {x : Word} (f : flag x) : target x := by
  obtain ⟨p,l,adj,P,L⟩ := f
  exact ⟨p,by simp [P],l,by simp [L],adj⟩

theorem positive_count {n} (data : Fin n → Word) (labels : Set (Fin n)) (h : hard data labels)
    (yes : ∀ k∈labels,flag (data k)) (no : ∀ k∉labels,Generic (data k)) :
    52 ≤ Fintype.card labels := by
  classical
  let E := univ.filter fun e : V × V => inc e.1 e.2
  have existsRow (e : E) : ∃ k : labels, pts (data k.val)={e.val.1} ∧ lines (data k.val)={e.val.2} := by
    obtain ⟨k,hk,p,l⟩ := demands_flags data labels h yes no e.val.1 e.val.2 (mem_filter.mp e.property).2
    exact ⟨⟨k,hk⟩,p,l⟩
  choose row fits using existsRow
  have inj : Function.Injective row := by
    intro i j eq
    have ptsEq := (fits i).1.symm.trans ((congrArg (fun k : labels => pts (data k.val)) eq).trans (fits j).1)
    have linesEq := (fits i).2.symm.trans ((congrArg (fun k : labels => lines (data k.val)) eq).trans (fits j).2)
    apply Subtype.ext
    exact Prod.ext (by simpa using ptsEq) (by simpa using linesEq)
  calc
    52 = E.card := flag_count.symm
    _ = Fintype.card E := (Fintype.card_coe E).symm
    _ ≤ _ := Fintype.card_le_of_injective row inj

theorem negative_count {n} (data : Fin n → Word) (labels : Set (Fin n)) (h : hard data labels)
    (yes : ∀ k∈labels,flag (data k)) (no : ∀ k∉labels,Generic (data k)) :
    6 ≤ Fintype.card (↥(labelsᶜ) : Type) := by
  classical
  by_contra! few
  let N := (labelsᶜ).toFinset
  let s := N.toList
  have length : s.length ≤ 5 := by
    have e : s.length=Fintype.card (↥(labelsᶜ) : Type) := (length_toList _).trans (Set.toFinset_card _)
    omega
  let r : Fin 5 → Word := fun i => ((s.map data)[i.val]?).getD 0
  have gen (i : Fin 5) : Generic (r i) := by
    by_cases hi : i.val<s.length
    · have mem := List.getElem_mem (l:=s) hi
      have nc : s[i.val] ∉ labels := by exact Set.mem_toFinset.mp (mem_toList.mp mem)
      simpa [r,List.getElem?_eq_getElem hi] using no _ nc
    · have nil : s[i.val]?=none := List.getElem?_eq_none (by omega)
      have empty : Generic 0 := by decide +kernel
      simpa [r,nil] using empty
  apply more_than_five data labels h (fun k hk => flag_has_edge (yes k hk)) no
  refine ⟨r,gen,?_⟩
  intro k hk
  have mem : k∈s := by simpa [s,N] using hk
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  refine ⟨⟨i,by omega⟩,?_⟩
  simp [r,List.getElem?_eq_getElem hi,eq]

theorem sample_count {n} (data : Fin n → Word) (labels : Set (Fin n)) (h : hard data labels)
    (yes : ∀ k∈labels,flag (data k)) (no : ∀ k∉labels,Generic (data k)) : 58 ≤ n := by
  classical
  have p := positive_count data labels h yes no
  have l := negative_count data labels h yes no
  have all := Fintype.card_subtype_compl (fun k : Fin n => k∈labels)
  change Fintype.card (↥(labelsᶜ) : Type) = Fintype.card (Fin n)-Fintype.card labels at all
  simp only [Fintype.card_fin] at all
  omega

end PEqualNP.Research.SampleCount

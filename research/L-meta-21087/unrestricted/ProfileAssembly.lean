import ProfileGroups
namespace PEqualNP.Outside.Mask114591
theorem profileIfExcluded (allExcluded : excludedGroups.all (fun z => !(search 8 z.1 z.2)) = true) {t : Nat} {S : Finset Sig} (sub : S ⊆ rawInputs.toFinset) (hl : live 8 t S) :
    (t,rawInputs.filter (fun a => decide (a ∈ S))) ∈ listedProfiles := by
  let l := rawInputs.filter (fun a => decide (a ∈ S))
  have eq : l.toFinset = S := by
    ext a
    simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (sub h),h⟩⟩
  have nd : l.Nodup := (by decide : rawInputs.Nodup).filter _
  have hv : ∀ a ∈ l, valid a := fun a ha => rawInputs_valid a (List.mem_filter.mp ha).1
  have lin : live 8 t l.toFinset := eq ▸ hl
  have hc := live_card lin
  rw [List.toFinset_card_of_nodup nd] at hc
  have hsep := cuts_full hv lin
  have hit := search_complete 8 t l nd hv lin
  have row := List.all_eq_true.mp (coversProfiles ⟨t,by omega⟩) l (List.mem_sublists.mpr List.filter_sublist)
  by_contra hn
  have ng : listedProfiles.contains (t,l) = false := by simpa [l] using hn
  have mem : (t,l) ∈ excludedGroups := by
    exact (show (t,l) ∈ listedProfiles ∨ (t,l) ∈ excludedGroups by simpa [show ¬ 9 < l.length + t by omega,hsep] using row).resolve_left hn
  have nog := List.all_eq_true.mp allExcluded (t,l) mem
  simp [hit] at nog
end PEqualNP.Outside.Mask114591
#print axioms PEqualNP.Outside.Mask114591.profileIfExcluded

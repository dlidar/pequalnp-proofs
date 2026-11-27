import Coverage
import Batch0
import Batch1
namespace PEqualNP.Outside.Comparator9929
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem allRejected : allRoots.all reject = true := by simp [allRoots, checked0, checked1]
theorem front : ∀ t : Fin 13, rawInputs.sublists.all (fun ws =>
    decide (12 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top) || !(search 11 t.val ws)) = true := by
  intro t
  apply List.all_eq_true.mpr
  intro ws hw
  have hc := List.all_eq_true.mp (coverage t) ws hw
  cases h : (decide (12 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top)) with
  | true => simp [h]
  | false =>
    simp only [h, Bool.false_or] at hc ⊢
    have hm : (t.val, ws) ∈ allRoots := by simpa using hc
    exact List.all_eq_true.mp allRejected (t.val, ws) hm

theorem lower (C : Circuit) (hg : FanInTwo C) (hs : C.size ≤ 11) (he : Correct C) : False := by
  obtain ⟨t,S,hsub,hl⟩ := compress (get_build C hg he)
  let l := rawInputs.filter (fun a => decide (a ∈ S))
  have eq : l.toFinset = S := by
    ext a
    simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (hsub h),h⟩⟩
  have nd : l.Nodup := (by decide : rawInputs.Nodup).filter _
  have hv : ∀ a ∈ l, valid a := fun a ha => rawInputs_valid a (List.mem_filter.mp ha).1
  have hl5 := extend hs hl
  have lin : live 11 t l.toFinset := eq ▸ hl5
  have hc := live_card lin
  rw [List.toFinset_card_of_nodup nd] at hc
  have hsep := cuts_full hv lin
  have hit := search_complete 11 t l nd hv lin
  have row := List.all_eq_true.mp (front ⟨t,by omega⟩) l (List.mem_sublists.mpr List.filter_sublist)
  simp [show ¬12 < l.length + t by omega,hsep,hit] at row
end PEqualNP.Outside.Comparator9929

theorem exact_negation : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat) < (1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat))) 11) := by
  rintro ⟨C,h,s,r⟩
  exact PEqualNP.Outside.Comparator9929.lower C h s r
#print axioms exact_negation

import Coverage
import Batch0
import Batch1
namespace PEqualNP.Outside.Mask4294973
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem allRejected : allRoots.all reject = true := by
  simp only [allRoots, List.all_append, checked0, checked1, Bool.and_self]
theorem front : ∀ t : Fin 11, rawInputs.sublists.all (fun ws =>
    decide (10 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top) || !(search 9 t.val ws)) = true := by
  intro t
  apply List.all_eq_true.mpr
  intro ws hw
  have hc := List.all_eq_true.mp (coverage t) ws hw
  cases h : (decide (10 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top)) with
  | true => simp [h]
  | false =>
    simp only [h, Bool.false_or] at hc ⊢
    have hm : (t.val, ws) ∈ allRoots := by simpa using hc
    exact List.all_eq_true.mp allRejected (t.val, ws) hm

theorem lower (C : Circuit) (hg : FanInTwo C) (hs : C.size ≤ 9) (he : Correct C) : False := by
  obtain ⟨t,S,hsub,hl⟩ := compress (get_build C hg he)
  let l := rawInputs.filter (fun a => decide (a ∈ S))
  have eq : l.toFinset = S := by
    ext a
    simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (hsub h),h⟩⟩
  have nd : l.Nodup := (by decide : rawInputs.Nodup).filter _
  have hv : ∀ a ∈ l, valid a := fun a ha => rawInputs_valid a (List.mem_filter.mp ha).1
  have hl5 := extend hs hl
  have lin : live 9 t l.toFinset := eq ▸ hl5
  have hc := live_card lin
  rw [List.toFinset_card_of_nodup nd] at hc
  have hsep := cuts_full hv lin
  have hit := search_complete 9 t l nd hv lin
  have row := List.all_eq_true.mp (front ⟨t,by omega⟩) l (List.mem_sublists.mpr List.filter_sublist)
  simp [show ¬10 < l.length + t by omega,hsep,hit] at row
end PEqualNP.Outside.Mask4294973
theorem exact_negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294973 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,h,s,r⟩
  exact PEqualNP.Outside.Mask4294973.lower C h s r
#print axioms exact_negation

import Coverage
import Batch0
import Batch1
import Batch2
import Batch3
import Batch4
import Batch5
import Batch6
import Batch7
import Batch8
import Batch9
import Batch10
import Batch11
import Batch12
import Batch13
import Batch14
import Batch15
import Batch16
import Batch17
import Batch18
import Batch19
import Batch20
import Batch21
import Batch22
import Batch23
import Batch24
import Batch25
import Batch26
import Batch27
import Batch28
import Batch29
import Batch30
namespace PEqualNP.Outside.Mask5805
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem allRejected : allRoots.all reject = true := by
  simp only [allRoots, List.all_append, checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23, checked24, checked25, checked26, checked27, checked28, checked29, checked30, Bool.and_self]
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
end PEqualNP.Outside.Mask5805
theorem exact_negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) C) := by
  rintro ⟨C,h,s,r⟩
  exact PEqualNP.Outside.Mask5805.lower C h s r
#print axioms exact_negation

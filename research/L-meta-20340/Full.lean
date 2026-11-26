import Classification
import Pos0
import Pos1
import Pos2
import Pos3
import Pos4
import Pos5
import Pos6
import Pos7
import Pos8
import Pos9
namespace PlaneMask
def allW : List Witness := wits0 ++ wits1 ++ wits2 ++ wits3 ++ wits4 ++ wits5 ++ wits6 ++ wits7 ++ wits8 ++ wits9
theorem all_work : allW.all (fun w => decide (Works w)) = true := by simp [allW, work0, work1, work2, work3, work4, work5, work6, work7, work8, work9]
theorem good_matrix : ∀ r : Byte, represented r allW = allowed r := by decide +kernel
theorem exact_class (r c : Byte) : Fits r c ↔ (allowed r).getLsbD c.val = true := by
  refine ⟨necessary r c, ?_⟩
  intro h
  rw [←good_matrix] at h
  obtain ⟨w, hw, rfl, rfl⟩ := extract _ _ _ h
  exact works_fit _ (of_decide_eq_true (List.all_eq_true.mp all_work _ hw))
theorem exact_list (r c : Byte) : Fits r c ↔ ∃ w ∈ allW, r = w.r ∧ c = w.c := by
  constructor
  · intro h
    have q := necessary _ _ h
    rw [←good_matrix] at q
    exact extract _ _ _ q
  · rintro ⟨w,hw,rfl,rfl⟩
    exact works_fit _ (of_decide_eq_true (List.all_eq_true.mp all_work _ hw))
theorem count : allW.length = 58 ∧ (allW.map (fun w => (w.r,w.c))).Nodup := by decide +kernel
end PlaneMask
#print axioms PlaneMask.exact_class
#print axioms PlaneMask.exact_list
#print axioms PlaneMask.count

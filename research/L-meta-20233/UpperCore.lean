import SplitCore
namespace PlaneMask
theorem simple_of_le (s : Byte) (i j : Nat) (hi : i < 8) (h : send s i ≤ send s j) :
    simple s i j = true := by
  by_cases e : i = j
  · simp [simple,e]
  · cases hx : s.val.testBit i with
    | false => simp [simple,hx]
    | true =>
      have := h ⟨i,hi⟩
      simp [send,hx,e] at this
      exact ((by decide : ¬ (true ≤ false)) this).elim

def smallLE (r c : Byte) (a b : Cell) :=
  simple r (a.val/8) (b.val/8) && simple c (a.val%8) (b.val%8)
theorem collapse (r c : Byte) (a b : Cell) (h : obs r c a ≤ obs r c b) : smallLE r c a b = true := by
  simp only [smallLE,Bool.and_eq_true]
  exact ⟨simple_of_le _ _ _ (by omega) h.1,simple_of_le _ _ _ (by omega) h.2⟩
structure Witness where
  r : Byte
  c : Byte
  code : Nat
def Works (w : Witness) := ∀ a b : Cell,
    (smallLE w.r w.c a b = true → w.code.testBit a.val ≤ w.code.testBit b.val) ∧
    (target a → ¬ target b → smallLE (rev w.r) (rev w.c) a b = true →
      w.code.testBit a.val = true ∧ w.code.testBit b.val = false)
instance (w : Witness) : Decidable (Works w) := by unfold Works target; infer_instance
theorem works_fit (w : Witness) (ok : Works w) : Fits w.r w.c := by
  apply (SplitMonotoneFactor.four_row_criterion _ _ _).mpr
  intro a b c d ab cd ad
  have x := ((ok a b).2 ab.1 ab.2.1 (collapse _ _ _ _ ab.2.2)).1
  have y := ((ok c d).2 cd.1 cd.2.1 (collapse _ _ _ _ cd.2.2)).2
  have z := (ok a d).1 (collapse _ _ _ _ ad)
  rw [x,y] at z
  exact (by decide : ¬ (true ≤ false)) z

def represented (r : Byte) : List Witness → BitVec 256
  | [] => 0
  | w::ws => (if r = w.r then ((1 : BitVec 256) <<< w.c.val) else 0) ||| represented r ws
theorem extract (ws : List Witness) (r c : Byte) (hit : (represented r ws).getLsbD c.val = true) :
    ∃ w ∈ ws, r = w.r ∧ c = w.c := by
  induction ws with
  | nil => simp [represented] at hit
  | cons w ws ih =>
    simp only [represented,BitVec.getLsbD_or,Bool.or_eq_true] at hit
    rcases hit with h | h
    · split at h
      · rename_i hr
        refine ⟨w,by simp,hr,Fin.ext ?_⟩
        simp [BitVec.getLsbD_shiftLeft,c.isLt] at h
        omega
      · simp at h
    · obtain ⟨v,hv,hr,hc⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem w hv,hr,hc⟩
end PlaneMask
#print axioms PlaneMask.works_fit
#print axioms PlaneMask.extract

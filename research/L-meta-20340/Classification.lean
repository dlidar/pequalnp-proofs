import Cert0
import Cert1
import Cert2
import Cert3
import Cert4
import Cert5
import Cert6
import Cert7
namespace PlaneMask
theorem avoid0 (r c : Byte) (h : Fits r c) : (union r rules0).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified0 t ht)) r c h
theorem avoid1 (r c : Byte) (h : Fits r c) : (union r rules1).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified1 t ht)) r c h
theorem avoid2 (r c : Byte) (h : Fits r c) : (union r rules2).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified2 t ht)) r c h
theorem avoid3 (r c : Byte) (h : Fits r c) : (union r rules3).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified3 t ht)) r c h
theorem avoid4 (r c : Byte) (h : Fits r c) : (union r rules4).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified4 t ht)) r c h
theorem avoid5 (r c : Byte) (h : Fits r c) : (union r rules5).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified5 t ht)) r c h
theorem avoid6 (r c : Byte) (h : Fits r c) : (union r rules6).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified6 t ht)) r c h
theorem avoid7 (r c : Byte) (h : Fits r c) : (union r rules7).getLsbD c.val = false := avoid _ (fun t ht => of_decide_eq_true (List.all_eq_true.mp certified7 t ht)) r c h
def allowed (r : Byte) : BitVec 256 := match r.val with
  | 0 => 0x100000000000000010000000100010117
  | 1 => 0x10000000100000107
  | 2 => 0x100010113
  | 4 => 0x100000000000000010000000100000015
  | 8 => 0x100000000000000000000000100010105
  | 16 => 0x10000000000010107
  | 32 => 0x100000000000000000000000000010113
  | 64 => 0x100000000000000010000000000010015
  | 128 => 0x100000000000000010000000100000013
  | 255 => 0x8000000000000000000000000000000000000000000000000000000000000000
  | _ => 0
def barred (r : Byte) : BitVec 256 := union r rules0 ||| union r rules1 ||| union r rules2 ||| union r rules3 ||| union r rules4 ||| union r rules5 ||| union r rules6 ||| union r rules7
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem matrix : ∀ r : Byte, barred r = ~~~(allowed r) := by decide +kernel
theorem necessary (r c : Byte) (h : Fits r c) : (allowed r).getLsbD c.val = true := by
  have hx : (barred r).getLsbD c.val = false := by simp only [barred,BitVec.getLsbD_or,avoid0 r c h, avoid1 r c h, avoid2 r c h, avoid3 r c h, avoid4 r c h, avoid5 r c h, avoid6 r c h, avoid7 r c h, Bool.or_self]
  rw [matrix,BitVec.getLsbD_not] at hx
  simpa [c.isLt] using hx
def singletonMask (i : Nat) : Nat := 2^i
def form (r c : Byte) := (r.val=0 ∧ c.val=0) ∨ (r.val=255 ∧ c.val=255) ∨ (∃ i : Fin 8, r.val=singletonMask i.val ∧ c.val=0) ∨ (∃ j : Fin 8, r.val=0 ∧ c.val=singletonMask j.val) ∨ (∃ i j : Fin 8, r.val=singletonMask i.val ∧ c.val=singletonMask j.val ∧ (1885146376704737940 : Nat).testBit (8*i.val+j.val) = false)
end PlaneMask
#print axioms PlaneMask.necessary

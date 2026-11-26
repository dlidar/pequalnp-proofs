from shared_profiles import raw,mask,pairs
from pathlib import Path
from itertools import product
d=Path(__file__).resolve().parent
word=[(1<<(r//5))|(1<<(4+r%5)) for r in range(20)]
def le(s,a,b):return (word[a]&s&~word[b])==0
good=[];table=[]
for s in range(512):
 need=[(a,b) for a,b in pairs if le(s^511,a,b)]
 bad=next(((a,b,c,h) for (a,b),(c,h) in product(need,repeat=2) if le(s,a,h)),None)
 if bad:
  a,b,c,h=bad;table.append(a+20*(b+20*(c+20*h)))
 else:
  f=sum(1<<x for x in range(20) if any(le(s,a,x) for a,b in need))
  assert all(not (le(s,a,b) and f>>a&1 and not (f>>b&1)) for a,b in product(range(20),repeat=2))
  assert all(f>>a&1 and not (f>>b&1) for a,b in need)
  good.append((s,f));table.append(0)
src='''import FactorCriterion
namespace Mask245567Splits
open SplitMonotoneFactor

structure Signals where
  bits : BitVec 9

instance : Preorder Signals where
  le x y := (x.bits &&& y.bits) = x.bits
  le_refl x := by simp
  le_trans x y z h1 h2 := by
    change x.bits &&& y.bits = x.bits at h1
    change y.bits &&& z.bits = y.bits at h2
    calc
      _ = (x.bits &&& y.bits) &&& z.bits := by rw [h1]
      _ = _ := by rw [BitVec.and_assoc,h2,h1]

instance (x y : Signals) : Decidable (x ≤ y) := inferInstanceAs (Decidable ((x.bits &&& y.bits) = x.bits))

abbrev R := Fin 20
def value (a : R) : Prop := (245567 : Nat).testBit a.val = true
instance (a : R) : Decidable (value a) := inferInstanceAs (Decidable (_ = true))
def row (a : R) : BitVec 9 := (1 <<< (a.val / 5)) ||| (1 <<< (4 + a.val % 5))
def left (s : Nat) (a : R) : Signals := ⟨BitVec.ofNat 9 s &&& row a⟩
def right (s : Nat) (a : R) : Signals := ⟨~~~(BitVec.ofNat 9 s) &&& row a⟩
abbrev req (s : Nat) (a b : R) := value a ∧ ¬ value b ∧ right s a ≤ right s b
def Fits (s : Nat) := Factors (left s) (right s) value
def masks : List Nat := MASKS
def cache (s : Nat) : Nat := match s with
CACHE
  | _ => 0
def mark (s : Nat) (a : R) := (cache s).testBit a.val

def cacheOK (s : Nat) := ∀ a b : R,
  (left s a ≤ left s b → mark s a ≤ mark s b) ∧
  (req s a b → mark s a = true ∧ mark s b = false)
instance (s : Nat) : Decidable (cacheOK s) := by unfold cacheOK; infer_instance

theorem caches_work : masks.all (fun s => decide (cacheOK s)) = true := by
  set_option maxRecDepth 32000 in decide +kernel

def badTable : Array Nat := #[BAD]
def coord (k j : Nat) : R := ⟨k / (20^j) % 20, Nat.mod_lt _ (by decide)⟩
def Bad (s : Nat) : Prop :=
  let k := badTable[s]?.getD 0
  req s (coord k 0) (coord k 1) ∧ req s (coord k 2) (coord k 3) ∧ left s (coord k 0) ≤ left s (coord k 3)
instance (s : Nat) : Decidable (Bad s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem all_cases : ∀ s : Fin 512, s.val ∈ masks ∨ Bad s.val := by
  set_option maxRecDepth 32000 in decide +kernel

theorem factor_masks (s : Fin 512) : Fits s.val ↔ s.val ∈ masks := by
  constructor
  · intro fit
    rcases all_cases s with good | ⟨ab, cd, ad⟩
    · exact good
    · exact False.elim (((four_row_criterion _ _ _).mp fit _ _ _ _ ab cd) ad)
  · intro good
    have ok : cacheOK s.val := of_decide_eq_true (List.all_eq_true.mp caches_work _ good)
    apply (four_row_criterion _ _ _).mpr
    intro a b c d ab cd ad
    have hx := (ok a b).2 ab
    have hy := (ok c d).2 cd
    have ht := (ok a d).1 ad
    rw [hx.1,hy.2] at ht
    exact (by decide : ¬ (true ≤ false)) ht

theorem proper_nontrivial : (masks.filter fun s => decide (1 < ((List.range 9).countP (fun i => s.testBit i)) ∧ ((List.range 9).countP (fun i => s.testBit i)) < 9)) = PROPER := by decide +kernel
end Mask245567Splits
#print axioms Mask245567Splits.factor_masks
#print axioms Mask245567Splits.proper_nontrivial
'''
src=src.replace('MASKS',str([s for s,c in good])).replace('CACHE','\n'.join(f'  | {s} => {c}' for s,c in good)).replace('BAD',','.join(map(str,table))).replace('PROPER',str([s for s,c in good if 1<s.bit_count()<9]))
(d/'CacheSplits.lean').write_text(src)

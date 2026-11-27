import Linearity
import Signature
import Balance
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def measuredCost (a : BitVec 8) : ℕ := ((0x9351d49c7254a45244636ec4dc52592d92d4e52dc8e46a475d5144d350b96d7246e3292b6d75d96595cb6d75d9654d369ab2caebb6d8ecb2caebb6d49171b923b6c66269a8a2aeb91391c8d9b1ab64b64b228da95b70a922912b238d2ae2690 : ℕ) >>> (3*a.toNat)) &&& 7

def cut (t : Fin 8) (a : Fin 9) : Bool :=
  let r := ([5,6,10,3,9,12,2,4] : List ℕ).getD t.val 0
  match a.val with
  | 0 | 8 => false
  | 3 | 4 | 5 => true
  | 1 => r.testBit 0
  | 2 => r.testBit 1
  | 6 => r.testBit 2
  | _ => r.testBit 3
def inputs (t : Fin 8) := pref (List.ofFn (cut t))
theorem input_length : ∀ t : Fin 8, (inputs t).length = 11 := by decide +kernel
def values (C : Circuit) (j : ℕ) (t : Fin 8) := (C.wires (inputs t)).getD j false
def price (C : Circuit) (j : ℕ) := measuredCost (signature (values C j))
theorem input_price (C : Circuit) : ((List.range 11).map (price C)).sum = 4 := by
  have h : ∀ j ∈ List.range 11, price C j = measuredCost (signature (fun t => (inputs t).getD j false)) := by
    intro j hj
    unfold price
    congr 2
    funext t
    exact wires_low C _ _ (by rw [input_length]; exact List.mem_range.mp hj)
  rw [List.map_congr_left h]
  decide +kernel

variable (pair_cost : ∀ a b : BitVec 8, measuredCost (a &&& b) ≤ measuredCost a + measuredCost b ∧ measuredCost (a ||| b) ≤ measuredCost a + measuredCost b)
variable (not_cost : ∀ a : BitVec 8, measuredCost (~~~a) = measuredCost a)

include pair_cost not_cost
theorem step_price {C : Circuit} (hb : ReadsBack 11 C) (j : Fin C.gates.length)
    (hl : Legal (11+j.val) (C.gates.get j)) :
    price C (11+j.val) ≤ (((C.gates.get j).inputs.map (price C)).sum) := by
  have hw (t : Fin 8) : values C (11+j.val) t = (C.gates.get j).op.eval
      ((C.gates.get j).inputs.map fun a => values C a t) :=
    wires_gate 11 C (inputs t) (input_length t) hb j.val j.isLt
  rcases hl with ⟨hop,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
  · have hv : values C (11+j.val) = fun t => !(values C a t) := by
      funext t
      rw [hw t,hop,hin]
      rfl
    rw [hin]
    simp [price,hv,sig_not,not_cost]
  · rcases hop with hop|hop
    · have hv : values C (11+j.val) = fun t => values C a t && values C b t := by
        funext t
        rw [hw t,hop,hin]
        simp [GateOp.eval]
      rw [hin]
      simpa [price,hv,sig_and] using (pair_cost (signature (values C a)) (signature (values C b))).1
    · have hv : values C (11+j.val) = fun t => values C a t || values C b t := by
        funext t
        rw [hw t,hop,hin]
        simp [GateOp.eval]
      rw [hin]
      simpa [price,hv,sig_or] using (pair_cost (signature (values C a)) (signature (values C b))).2

theorem conditional_impossible (gs : List Gate) (o : ℕ) (sz : gs.length ≤ 10) (out : o+1 = 11+gs.length)
    (hg : ∀ j : Fin (first::second::gs).length, Legal (9+j.val) ((first::second::gs).get j))
    (live : ∀ j : Fin (first::second::gs).length, j.val+1 < (first::second::gs).length →
      ∃ k : Fin (first::second::gs).length, j.val < k.val ∧ 9+j.val ∈ ((first::second::gs).get k).inputs)
    (he : ∀ x, (Circuit.mk (first::second::gs) o).eval (List.ofFn x) = perm3 x) : False := by
  let D : Circuit := ⟨gs,o⟩
  have hl := tail_legal hg
  have hb := backward o hl
  have hp := wire_perm gs o sz out hl live he
  have le := output_budget (price D) 11 gs o hp (fun j => step_price pair_cost not_cost hb j (hl j))
  rw [input_price] at le
  have eq : values D o = fun t => perm3 (cut t) := funext fun t => he (cut t)
  have five : measuredCost (signature fun t => perm3 (cut t)) = 5 := by decide +kernel
  simp [price,eq,five] at le
end PEqualNP.Research.Permanent27300

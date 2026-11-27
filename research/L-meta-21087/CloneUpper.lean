import Family
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Family Mask114591Support
namespace Mask114591CloneUpper

def circuit (l : Nat) : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.or,[8,1]⟩, ⟨.or,[2,4]⟩, ⟨.or,[l+2,5]⟩,
    ⟨.and,[l+1,l+3]⟩, ⟨.not,[l+4]⟩, ⟨.or,[l,l+3]⟩, ⟨.and,[l+6,l+5]⟩],l+7⟩

def formula (a b c d e f : Bool) : Bool :=
  let t := c || d || e
  ((a || b) || t) && !((f || b) && t)

theorem eval_eq (x : List Bool) (l : Nat) (hl : x.length = l) (hn : 9 ≤ l) :
    (circuit l).eval x = formula (x.getD 0 false) (x.getD 1 false) (x.getD 2 false)
      (x.getD 4 false) (x.getD 5 false) (x.getD 8 false) := by
  simp (disch := omega) only [Circuit.eval,Circuit.wires,circuit,List.foldl_cons,List.foldl_nil,
    List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.all_cons,List.any_nil,List.all_nil,
    List.headD_cons,id_eq,Bool.or_false,Bool.and_true,append_bit,List.length_append,List.length_singleton,
    hl,ite_true,ite_false,if_pos,if_neg,formula,Nat.add_assoc]

theorem at_base (u : Fin 4) (v : Fin 5) :
    formula (decide (0 = u.val ∨ 0 = 4+v.val)) (decide (1 = u.val ∨ 1 = 4+v.val))
       (decide (2 = u.val ∨ 2 = 4+v.val)) (decide (4 = u.val ∨ 4 = 4+v.val))
       (decide (5 = u.val ∨ 5 = 4+v.val)) (decide (8 = u.val ∨ 8 = 4+v.val)) = base u v := by
  revert u v
  decide

theorem cloned_upper (k : Nat) : ∃ C : Circuit, FanInTwo C ∧ C.size = 8 ∧
    (C.gates.filter (fun g => match g.op with | .not => true | _ => false)).length = 1 ∧
    Represents (clone k) C := by
  refine ⟨circuit (4+(5+k)), ?_, rfl, rfl, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · intro u v
    rw [eval_eq _ _ (by simp [oneEach]; omega) (by omega)]
    simp only [oneEach_bit,clone]
    rw [← at_base]
    by_cases hv : v.val < 5
    · simp [project,hv]
    · have hv' : 5 ≤ v.val := by omega
      have sep : ∀ i : Nat, i ≤ 8 → i ≠ 4 + v.val := by intro i hi; omega
      have vn : v ≠ 0 := by intro he; subst v; simp at hv
      simp only [project,dif_neg hv]
      change _ = formula (decide (0 = u.val ∨ 0 = 6)) (decide (1 = u.val ∨ 1 = 6))
        (decide (2 = u.val ∨ 2 = 6)) (decide (4 = u.val ∨ 4 = 6))
        (decide (5 = u.val ∨ 5 = 6)) (decide (8 = u.val ∨ 8 = 6))
      simp (disch := decide) [vn,sep 0 (by decide),sep 1 (by decide),sep 2 (by decide),
        sep 4 (by decide),sep 5 (by decide),sep 8 (by decide)]

end Mask114591CloneUpper
#print axioms Mask114591CloneUpper.cloned_upper

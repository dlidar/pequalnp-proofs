import PEqualNP.Research.PlaneRuleCost

namespace PEqualNP.Research.PlaneLocalCost
open Finset PEqualNP.Research.PlaneORDepth PEqualNP.Research.PlaneRuleDepth PEqualNP.Research.PlaneRuleCost

def zeros (x : Input) := univ.filter fun i => x i=false
def raise (x : Input) (i : Bit) : Input := fun j => decide (i=j) || x j

theorem raised_edge (x : Input) (maximalX : maximal x) (i : Bit) (off : x i=false) :
    graph (raise x i)=true := by
  apply Bool.eq_true_of_not_eq_false
  intro no
  have eq := maximalX.2 _ ((independent_iff _).mpr no) (by intro j on; simp [raise,on])
  have yes : raise x i i=true := by simp [raise]
  rw [eq,off] at yes; cases yes

theorem lower (x : Input) (maximalX : maximal x) (rs last)
    (pos : ∀ p l,adjacent p l=true → valOut rs last (pair p l)=true)
    (neg : valOut rs last x=false) : (zeros x).card ≤ rs.length+1 := by
  classical
  obtain ⟨q,hq,miss⟩ := failed_operand _ _ neg
  have zero : dark (rs.foldl valStep (initial x)) {q} := by intro j hj; rw [mem_singleton.mp hj]; exact miss
  obtain ⟨T,m,off,forces⟩ := pull_many rs _ _ zero
  have sub : (zeros x).image Fin.val ⊆ T := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    by_contra hn
    obtain ⟨p,l,adj,hp,hl⟩ := of_decide_eq_true (raised_edge x maximalX i (mem_filter.mp hi).2)
    have stay : dark (initial (pair p l)) T := by
      intro j hj
      rw [get_raw]
      split
      next hj42 =>
        let k : Bit := ⟨j,hj42⟩
        have black := off j hj
        rw [get_raw,dite_eq_left hj42] at black
        have ne : i≠k := fun eq => hn ((congrArg Fin.val eq).symm ▸ hj)
        have notOn : raise x i k=false := by simp [raise,ne,black,k] 
        apply Bool.eq_false_iff.mpr
        intro yes
        rcases (of_decide_eq_true yes : k=Fin.castAdd 21 p ∨ k=Fin.natAdd 21 l) with e|e <;>
          rw [e] at notOn <;> simp_all
      next => rfl
    have falseAt := forces _ (by simp [initial]) stay q (mem_singleton_self _)
    have trueAt := (of_decide_eq_true (pos p l adj)) q hq
    change (rs.foldl valStep (initial (pair p l))).getD q false=true at trueAt
    simp_all
  have n := card_le_card sub
  rw [card_image_of_injective _ Fin.val_injective] at n
  simp only [card_singleton] at m
  omega

def wires (rs : List Rule) (x : Input) := rs.foldl valStep (initial x)
theorem wire_length (rs : List Rule) (v : List Bool) :
    (rs.foldl valStep v).length=v.length+rs.length := by
  induction rs generalizing v with
  | nil => simp
  | cons r rs ih => simp [ih,valStep];omega

theorem preserve (rs : List Rule) (v : List Bool) (i : ℕ) (hi : i<v.length) :
    (rs.foldl valStep v).getD i false = v.getD i false := by
  induction rs generalizing v with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons,ih (valStep v r) (by simp [valStep];omega)]
    exact List.getD_append _ _ _ _ hi

def legal (rs : List Rule) := ∀ j (hj:j<rs.length), ∀ i∈rs[j].1 ∪ rs[j].2,i<43+j

theorem chain (a : Bit) (s : List Bit) : ∃ (rs : List Rule) (last : ℕ),
    legal rs ∧ last < 43+rs.length ∧ rs.length=s.length ∧
    ∀ x, (wires rs x).getD last false = (a::s).any x := by
  induction s using List.reverseRecOn with
  | nil =>
    refine ⟨[],a.val,by simp [legal],by have := a.isLt;omega,by simp,?_⟩
    intro x; simp only [wires,List.foldl_nil,get_raw,dite_eq_left a.isLt,List.any_cons,List.any_nil,Bool.or_false]
  | append_singleton s b ih =>
    obtain ⟨rs,last,leg,valid,len,ev⟩ := ih
    let gate : Rule := ({last},{b.val})
    refine ⟨rs++[gate],43+rs.length,?_,by simp,by simp [len],?_⟩
    · intro j hj i hi
      by_cases lt : j<rs.length
      · rw [List.getElem_append_left lt] at hi; exact leg j lt i hi
      · have ej : j=rs.length := by simp at hj;omega
        subst j
        simp [gate] at hi
        rcases hi with rfl|rfl
        · exact valid
        · have := b.isLt;omega
    · intro x
      let w := wires rs x
      have length : w.length=43+rs.length := by simp only [w,wires,wire_length,initial,List.length_append,List.length_ofFn,List.length_singleton]
      have left := ev x
      have right : w.getD b.val false=x b := by
        rw [show w=rs.foldl valStep (initial x) from rfl,preserve _ _ _ (by simp only [initial,List.length_append,List.length_ofFn,List.length_singleton];have := b.isLt;omega),get_raw,dite_eq_left b.isLt]
      change (List.foldl valStep (initial x) (rs ++ [gate])).getD (43+rs.length) false = _
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change (w ++ [valOp w {last} || valOp w {b.val}]).getD (43+rs.length) false = _
      rw [←length,List.getD_append_right _ _ _ _ le_rfl]
      change w.getD last false = _ at left
      simp only [List.getD_eq_getElem?_getD] at left right
      simp [valOp,left,right,List.any_append,Bool.or_assoc]
      have e : decide (∃ u ∈ s,x u=true) = s.any x := Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq,List.any_eq_true])
      rw [e]

theorem sharp (x : Input) (mx : maximal x) :
    IsLeast {k : ℕ | ∃ (rs : List Rule) (j : ℕ), legal rs ∧ j<43+rs.length ∧ rs.length=k ∧
      (∀ p l, adjacent p l=true → valOut rs {j} (pair p l)=true) ∧ valOut rs {j} x=false}
    ((zeros x).card-1) := by
  classical
  have adj : adjacent 0 0=true := by decide
  have nz := mx.1 0 0 adj
  have nonempty : (zeros x).Nonempty := by
    rcases nz with h|h <;> exact ⟨_,mem_filter.mpr ⟨mem_univ _,h⟩⟩
  have ne : (zeros x).toList ≠ [] := by simpa using nonempty.ne_empty
  obtain ⟨a,s,id⟩ := List.exists_cons_of_ne_nil ne
  obtain ⟨rs,j,leg,back,len,ev⟩ := chain a s
  have size : (zeros x).card=s.length+1 := by simp [←length_toList,id]
  have out (y : Input) : valOut rs {j} y=true ↔ ∃ i∈zeros x,y i=true := by
    change valOp (wires rs y) {j}=true ↔ _
    simp only [valOp,decide_eq_true_eq,mem_singleton,forall_eq,ev,←id,List.any_eq_true,mem_toList]
  constructor
  · refine ⟨rs,j,leg,back,by omega,?_,?_⟩
    · intro p l e
      apply (out _).mpr
      rcases mx.1 p l e with h|h
      · exact ⟨_,mem_filter.mpr ⟨mem_univ _,h⟩,by simp [pair]⟩
      · exact ⟨_,mem_filter.mpr ⟨mem_univ _,h⟩,by simp [pair]⟩
    · apply Bool.eq_false_iff.mpr
      intro h; obtain ⟨i,hi,yes⟩ := (out x).mp h
      have no := (mem_filter.mp hi).2;simp_all
  · rintro k ⟨rs,j,_,_,rfl,yes,no⟩
    have := lower x mx rs {j} yes no; omega

end PEqualNP.Research.PlaneLocalCost

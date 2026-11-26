import PEqualNP.Research.PlaneRuleDepth

namespace PEqualNP.Research.PlaneRuleCost
open Finset PEqualNP.Research.PlaneORDepth PEqualNP.Research.PlaneRuleDepth

def dark (w : List Bool) (S : Finset ℕ) := ∀ i∈S,w.getD i false=false

theorem failed_operand (w : List Bool) (S : Finset ℕ) (h : valOp w S=false) :
    ∃ i∈S,w.getD i false=false := by
  by_contra! n
  have all : valOp w S=true := decide_eq_true (fun i hi => Bool.eq_true_of_not_eq_false (n i hi))
  simp_all

theorem old_wire (w : List Bool) (b : Bool) (i : ℕ) (ne : i≠w.length) :
    (w++[b]).getD i false = w.getD i false := by
  by_cases hi : i<w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have k : i-w.length≠0 := by omega
    cases e : i-w.length with
    | zero => contradiction
    | succ j => simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show w.length ≤ i by omega)]

/-- Pull a set of simultaneously false wires back across one shared rule, paying at most one extra wire. -/
theorem pull (w : List Bool) (r : Rule) (S : Finset ℕ) (h : dark (valStep w r) S) :
    ∃ T : Finset ℕ, T.card ≤ S.card+1 ∧ dark w T ∧
    ∀ v : List Bool,v.length=w.length → dark v T → dark (valStep v r) S := by
  classical
  by_cases needed : w.length ∈ S
  · have gate := h _ needed
    have atNew (v : List Bool) : (valStep v r).getD v.length false = (valOp v r.1 || valOp v r.2) := by
      unfold valStep;rw [List.getD_append_right _ _ _ _ le_rfl];simp
    rw [atNew] at gate
    obtain ⟨l,k⟩ := Bool.or_eq_false_iff.mp gate
    obtain ⟨a,ha,za⟩ := failed_operand _ _ l
    obtain ⟨b,hb,zb⟩ := failed_operand _ _ k
    let U := S.erase w.length
    refine ⟨insert a (insert b U),?_,?_,?_⟩
    · have e := card_erase_add_one needed
      have h1 := card_insert_le b U
      have h2 := card_insert_le a (insert b U)
      dsimp [U] at *;omega
    · intro i hi
      rcases mem_insert.mp hi with rfl|hi
      · exact za
      rcases mem_insert.mp hi with rfl|rest
      · exact zb
      obtain ⟨ne,mem⟩ := mem_erase.mp rest
      simpa only [valStep,old_wire _ _ _ ne] using h i mem
    · intro v len ok i hi
      by_cases eq : i=w.length
      · have atI : i=v.length := eq.trans len.symm
        rw [atI,atNew,Bool.or_eq_false_iff]
        have fail (Q : Finset ℕ) (j : ℕ) (mem : j∈Q) (z : v.getD j false=false) : valOp v Q=false := by
          apply Bool.eq_false_iff.mpr;intro g;have e := (of_decide_eq_true g) j mem;simp_all
        exact ⟨fail _ _ ha (ok a (by simp)),fail _ _ hb (ok b (by simp))⟩
      · have ne : i≠v.length := by omega
        rw [valStep,old_wire _ _ _ ne]
        exact ok i (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨eq,hi⟩)))
  · refine ⟨S,by omega,?_,?_⟩
    · intro i hi;have ne : i≠w.length := fun e => needed (e ▸ hi)
      simpa only [valStep,old_wire _ _ _ ne] using h i hi
    · intro v len ok i hi
      have ne : i≠v.length := fun e => needed ((e.trans len) ▸ hi)
      rw [valStep,old_wire _ _ _ ne];exact ok i hi

theorem pull_many (rs : List Rule) (w : List Bool) (S : Finset ℕ) (h : dark (rs.foldl valStep w) S) :
    ∃ T : Finset ℕ,T.card ≤ S.card+rs.length ∧ dark w T ∧
    ∀ v : List Bool,v.length=w.length → dark v T → dark (rs.foldl valStep v) S := by
  induction rs generalizing w S with
  | nil => exact ⟨S,by simp,h,fun _ _ ok => ok⟩
  | cons r rs ih =>
    obtain ⟨U,m,z,carry⟩ := ih (valStep w r) S h
    obtain ⟨T,n,t,first⟩ := pull w r U z
    refine ⟨T,by simp;omega,t,?_⟩
    intro v len ok
    exact carry _ (by simp [valStep,len]) (first v len ok)

def initial (x : Input) := List.ofFn x ++ [false]
theorem get_raw (x : Input) (i : ℕ) : (initial x).getD i false = if h : i<42 then x ⟨i,h⟩ else false := by
  by_cases hi : i<42
  · rw [initial,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hi),dite_eq_left hi]
    rw [List.getD_eq_getElem?_getD]; simp only [List.getElem?_ofFn,hi,dite_eq_left,Option.getD_some]
  · have h : 42 ≤ i := by omega
    rw [initial,List.getD_append_right _ _ _ _ (by simpa using h)]
    simp [hi]

theorem cost (rs last) (pos : ∀ p l,adjacent p l=true → valOut rs last (pair p l)=true)
    (neg : valOut rs last extremal=false) : 33 ≤ rs.length := by
  classical
  obtain ⟨q,hq,miss⟩ := failed_operand _ _ neg
  have zero : dark (rs.foldl valStep (initial extremal)) {q} := by intro j hj; rw [mem_singleton.mp hj]; exact miss
  obtain ⟨T,m,off,forces⟩ := pull_many rs _ _ zero
  have sub : holes.image Fin.val ⊆ T := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    by_contra hn
    obtain ⟨p,l,adj,hp,hl⟩ := of_decide_eq_true (indispensable i (mem_filter.mp hi).2)
    have stay : dark (initial (pair p l)) T := by
      intro j hj
      rw [get_raw]
      split
      next hj42 =>
        let k : Bit := ⟨j,hj42⟩
        have black := off j hj
        rw [get_raw,dite_eq_left hj42] at black
        have ne : i≠k := fun eq => hn ((congrArg Fin.val eq).symm ▸ hj)
        have notOn : PlaneORDepth.flip i k=false := by simp [PlaneORDepth.flip,ne,black,k] 
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
  rw [card_image_of_injective _ Fin.val_injective,holes_card] at n
  simp only [card_singleton] at m
  omega

end PEqualNP.Research.PlaneRuleCost

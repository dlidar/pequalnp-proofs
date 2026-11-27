import Restrict
import PEqualNP.Research.L_meta_2071_flag_pinning

open PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Mask114591Family Mask114591Support Mask114591Restrict

namespace Mask114591ClonePin

theorem ancestors_omit (j n : Nat) (gs : List Gate) (s : Finset Nat) (hs : j ∉ s)
    (h : ∀ g ∈ gs, j ∉ g.inputs) : j ∉ ancestors n gs s := by
  induction gs generalizing n with
  | nil => exact hs
  | cons g gs ih =>
    have hr := ih (n+1) (fun a ha => h a (.tail _ ha))
    have hg := h g (.head _)
    simp only [ancestors]
    split_ifs <;> simp_all

def bits {n m : Nat} (u : Fin n) (v : Fin m) (i : Fin (n+m)) :=
  decide (i.val = u.val ∨ i.val = n+v.val)

theorem bits_list {n m : Nat} (u : Fin n) (v : Fin m) :
    List.ofFn (bits u v) = oneEach u v := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro i ha hb
    rw [← List.getD_eq_getElem _ false hb,oneEach_bit]
    simp [bits]

theorem delete_column {n a : Nat} {A : Fin n → Fin a → Bool} {B : Fin n → Fin (a+1) → Bool}
    (ext : ∀ u v, B u ⟨v.val,by omega⟩ = A u v)
    (witness : ∃ u v, B u (Fin.last a) = true ∧ A u v = false)
    (other : ∃ u v, A u v = true)
    {C : Circuit} (hc : Monotone2 C) (hr : Represents B C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧ Represents A D := by
  obtain ⟨u,v,ht,hf⟩ := witness
  let j : Fin (n+(a+1)) := ⟨n+a,by omega⟩
  let w : Fin (a+1) := ⟨v.val,by omega⟩
  have eh : C.eval (oneEach u (Fin.last a)) = true := (hr _ _).trans ht
  have el : C.eval (oneEach u w) = false := (hr _ _).trans ((ext _ v).trans hf)
  have no : C.output ≠ j.val := by
    obtain ⟨u',v',ha⟩ := other
    let w' : Fin (a+1) := ⟨v'.val,by omega⟩
    have ex : C.eval (oneEach u' w') = true := (hr _ _).trans ((ext _ v').trans ha)
    intro he
    -- Raw input positions keep their original values throughout the circuit.
    have unchanged (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
        (gs.foldl step x).getD i false = x.getD i false := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,ih (step x g) (by simp [step] <;> omega)]
        simp only [step,append_bit,if_neg (Nat.ne_of_lt hi)]
    change (C.gates.foldl step (oneEach u' w')).getD C.output false = true at ex
    rw [he,unchanged,oneEach_bit] at ex
    · simp only [decide_eq_true_eq] at ex
      change n+a = u'.val ∨ n+a = n+v'.val at ex
      omega
    · simp [j,oneEach] <;> omega
  have rd : ∃ g ∈ C.gates, j.val ∈ g.inputs := by
    by_contra! hn
    have ha := ancestors_omit j.val (n+(a+1)) C.gates {C.output}
      (by simpa [eq_comm] using no) hn
    let x := oneEach u (Fin.last a)
    let y := oneEach u w
    have hx : x.length = n+(a+1) := by simp [x,oneEach] <;> omega
    have hy : y.length = x.length := by simp [x,y,oneEach]
    have cmp : agrees x y (ancestors x.length C.gates {C.output}) := by
      intro i hi
      rw [hx] at hi
      have ne : i ≠ j.val := fun h => ha (h ▸ hi)
      change i ≠ n+a at ne
      dsimp only [x,y]
      rw [oneEach_bit,oneEach_bit]
      simp only [Fin.val_last,decide_eq_true_eq]
      tauto
    have z := propagate C.gates (fun g hg => (hc g hg).1) x y hy.symm {C.output} cmp C.output (by simp) eh
    change C.eval (oneEach u w) = true at z
    simp [el] at z
  have pinned (x : Fin n) (v' : Fin a) :
      List.ofFn (fun i => if i ∈ ({j} : Finset _) then false else
        bits x (⟨v'.val, by omega⟩ : Fin (a+1)) i) =
      oneEach x (⟨v'.val,by omega⟩ : Fin (a+1)) := by
    rw [← bits_list]
    apply congrArg List.ofFn
    funext i
    by_cases he : i = j
    · subst i
      simp only [Finset.mem_singleton_self,ite_true,bits,j]
      symm
      apply decide_eq_false
      omega
    · simp [he]
  obtain ⟨R,hm,hs,hp⟩ := PEqualNP.Research.FlagPinning.pin_readers _ {j} C hc
    (by exact ⟨bits u w,(congrArg C.eval (pinned u v)).trans el⟩)
  refine ⟨trim (n+a) 1 R, trim_mono _ _ hm, ?_, ?_⟩
  · rw [trim_size]
    obtain ⟨g,hg,hrd⟩ := rd
    have pos : 0 < C.gates.countP (fun g => g.inputs.any fun k =>
        decide (∃ i ∈ ({j} : Finset _), i.val = k)) := by
      apply List.countP_pos_iff.mpr
      exact ⟨g,hg,List.any_eq_true.mpr ⟨j.val,hrd,by simp⟩⟩
    omega
  · apply trim_rep (A := A) (B := fun u v => R.eval (oneEach u v)) (fun _ _ => rfl)
    intro a' b'
    specialize hp (bits a' (⟨b'.val,by omega⟩ : Fin (a+1)))
    rw [bits_list,pinned] at hp
    exact hp.trans ((hr _ _).trans (ext _ _))

end Mask114591ClonePin
#print axioms Mask114591ClonePin.delete_column

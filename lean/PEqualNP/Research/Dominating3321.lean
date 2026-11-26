import PEqualNP.Research.FirstReader3321

namespace PEqualNP.Research.Dominating3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.Research.FirstReader3321 PEqualNP.Research.GateCuts3321

def centers {n : ℕ} (S : Finset ℕ) (i : Fin n) := decide (i.val ∉ S)

theorem gain {n k} (S : Finset ℕ) (f : Fn n) (inh : ∃ v : Fin n, v.val ∈ S)
    (valid : ∀ i ∈ S, i < n)
    (piv : ∀ v : Fin n, v.val ∈ S → cut f v false (centers S) ≠ cut f v true (centers S))
    (pair : ∀ v w : Fin n, v.val ∈ S → w.val ∈ S → v ≠ w →
       ∃ x, x w = true ∧ cut f v false x ≠ cut f v true x)
    (alive : ∀ v : Fin n, v.val ∈ S → ∃ x, cut f v false x = true)
    (lb : ∀ v : Fin n, v.val ∈ S → Lower (cut f v false) k)
    (C : Circuit) (mono : Monotone2 C) (ev : ∀ x, C.eval (List.ofFn x) = f x) :
    k+2 ≤ C.size := by
  classical
  by_contra! tiny
  have raw (v : Fin n) (x : Fin n → Bool) : (C.wires (List.ofFn x)).getD v.val false = x v :=
    vl_input C.gates x v v.isLt
  have out (v : Fin n) (hv : v.val ∈ S) : C.output ≠ v.val := by
    obtain ⟨x,hx⟩ := alive v hv
    intro eq
    have h := ev (Function.update x v false)
    change (C.wires _).getD C.output false = _ at h
    rw [eq,raw,Function.update_self] at h
    exact Bool.noConfusion (h.trans hx)
  have ex : ∃ g ∈ C.gates, Hit S g = true := by
    by_contra! none
    obtain ⟨v,hv⟩ := inh
    have av : ∀ t ∈ C.gates, v.val ∉ t.inputs := by
      intro t ht mem
      exact none t ht (by simpa [Hit] using (show ∃ j ∈ t.inputs, j ∈ S from ⟨_,mem,hv⟩))
    exact piv v hv ((ev _).symm.trans ((pivot_eq v C.gates (centers S) av C.output (out v hv)).trans (ev _)))
  obtain ⟨pre,g,post,split,hit,avoid⟩ := split_first (Hit S) C.gates ex
  obtain ⟨j,jin,js⟩ : ∃ j ∈ g.inputs, j ∈ S := by simpa [Hit] using hit
  let v : Fin n := ⟨j,valid j js⟩
  have hv : v.val ∈ S := js
  have before : ∀ t ∈ pre, v.val ∉ t.inputs := by
    intro t ht mem
    have no := avoid t ht
    have yes : Hit S t = true := by simpa [Hit] using (show ∃ i ∈ t.inputs, i ∈ S from ⟨_,mem,hv⟩)
    exact Bool.noConfusion (no.symm.trans yes)
  let F (x : Fin n → Bool) := Bit g (W pre x)
  let a := n + pre.length
  let A (x : Fin n → Bool) := W pre x ++ [F x]
  have len (x : Fin n → Bool) : (W pre x).length = a := by simp [W,length_wiresFrom,a]
  have finalw (x : Fin n → Bool) : C.wires (List.ofFn x) = wiresFrom post (A x) := by
    simp only [Circuit.wires,split,List.foldl_append,List.foldl_cons];rfl
  have at_a (x : Fin n → Bool) : (C.wires (List.ofFn x)).getD a false = F x := by
    rw [finalw,getD_wiresFrom _ _ _ (by simp [A,len]),show a = (W pre x).length from (len x).symm]
    exact getD_snoc_eq _ _ _
  have postops : ∀ t ∈ post, t.op = .and ∨ t.op = .or := by
    intro t ht;exact (mono t (by rw [split];simp [ht])).1
  have preops : ∀ t ∈ pre, t.op = .and ∨ t.op = .or := by
    intro t ht;exact (mono t (by rw [split];simp [ht])).1
  have budget (T : Finset ℕ) (vj : v.val ∈ T)
      (sound : ∀ x i, i ∈ T → (C.wires (List.ofFn (Function.update x v false))).getD i false = false) :
      ∀ t ∈ post, Hit T t = false := by
    have cnt := cap v C mono ev (lb v hv) T sound
    rw [split] at cnt
    exact tail_avoids T pre g post (by simpa [Hit] using
      (show ∃ i ∈ g.inputs, i ∈ T from ⟨v,jin,vj⟩)) (by omega)
  have raw0 (x) : (C.wires (List.ofFn (Function.update x v false))).getD v.val false = false := by
    rw [raw,Function.update_self]
  have impossible_zero (zero : ∀ x, F (Function.update x v false) = false) : False := by
    let T : Finset ℕ := {v.val,a}
    have sound (x i) (hi : i∈T) : (C.wires (List.ofFn (Function.update x v false))).getD i false = false := by
      rcases (show i=v.val ∨ i=a by simpa [T] using hi) with rfl|rfl
      · exact raw0 _
      · rw [at_a,zero]
    have oa : C.output ∉ T := by
      intro o
      obtain ⟨x,h⟩ := alive v hv
      exact Bool.noConfusion ((sound x _ o).symm.trans ((ev _).trans h))
    let x : Fin n → Bool := centers S
    let x0 := Function.update x v false
    let x1 := Function.update x v true
    have eq : ∀ i ∉ T, (A x0).getD i false = (A x1).getD i false := by
      intro i no
      obtain ⟨nv,na⟩ : i ≠ v.val ∧ i ≠ a := by simpa [T] using no
      simp only [A,getD_snoc_ne _ _ _ _ (show i ≠ (W pre x0).length by rw [len];exact na),
        getD_snoc_ne _ _ _ _ (show i ≠ (W pre x1).length by rw [len];exact na)]
      exact pivot_eq v pre x before i nv
    have e := equal_off T post postops (budget T (by simp [T]) sound) _ _
      (show (A x0).length = (A x1).length by simp [A,len]) eq _ oa
    rw [← finalw,← finalw] at e
    exact piv v hv ((ev _).symm.trans (e.trans (ev _)))
  have impossible_mask (x : Fin n → Bool) (pivotal : cut f v false x ≠ cut f v true x)
      (mask : F (Function.update x v false) = F (Function.update x v true)) : False := by
    let x0 := Function.update x v false
    let x1 := Function.update x v true
    have no := budget {v.val} (by simp) (fun x i hi => by simp only [Finset.mem_singleton] at hi;subst i;exact raw0 _)
    have noread : ∀ t ∈ post, v.val ∉ t.inputs := by
      intro t ht mem
      have yes : Hit {v.val} t = true := by simpa [Hit] using mem
      exact Bool.noConfusion ((no t ht).symm.trans yes)
    have head : ∀ i, i ≠ v.val → (A x0).getD i false = (A x1).getD i false := by
      intro i nv
      by_cases fixed : i=a
      · subst i;simpa only [A,getD_snoc_len _ _ _ _ (len _)] using mask
      · rw [show (A x0).getD i false = (W pre x0).getD i false from getD_snoc_ne _ _ _ _ (by rw [len];exact fixed),
            show (A x1).getD i false = (W pre x1).getD i false from getD_snoc_ne _ _ _ _ (by rw [len];exact fixed)]
        exact pivot_eq v pre x before i nv
    have e := agree_except v.val post _ _ noread (show (A x0).length = (A x1).length by simp [A,len]) head _ (out v hv)
    rw [← finalw,← finalw] at e
    exact pivotal ((ev _).symm.trans (e.trans (ev _)))
  have gmem : g ∈ C.gates := by rw [split];simp
  rcases (mono g gmem).1 with op|op
  · apply impossible_zero
    intro x
    have z : (W pre (Function.update x v false)).getD v.val false = false := by
      rw [show (W pre (Function.update x v false)).getD v.val false = (Function.update x v false) v from vl_input _ _ _ v.isLt,Function.update_self]
    apply Bool.eq_false_iff.mpr
    intro yes
    have every : ∀ i ∈ g.inputs, (W pre (Function.update x v false)).getD i false = true := by
      simpa [F,Bit,op,GateOp.eval] using yes
    exact Bool.noConfusion (z.symm.trans (every _ jin))
  · have hop : g.op = .or := op
    have on (x : Fin n → Bool) : F x = true ↔ ∃ i ∈ g.inputs, (W pre x).getD i false = true := by
      simp [F,Bit,hop,GateOp.eval]
    by_cases dead : ∀ x, F (Function.update x v false) = false
    · exact impossible_zero dead
    push_neg at dead
    obtain ⟨x,high⟩ := dead
    obtain ⟨w,mem,yes⟩ := (on _).mp (by simpa using high)
    have ne : w ≠ v.val := by
      intro e;subst w
      have h := vl_input pre (Function.update x v false) v v.isLt
      exact Bool.noConfusion (yes.symm.trans (h.trans (Function.update_self _ _ _)))
    by_cases special : w ∈ S
    · let u : Fin n := ⟨w,valid _ special⟩
      obtain ⟨y,yu,hy⟩ := pair v u hv special (fun e => ne (congrArg Fin.val e.symm))
      apply impossible_mask y hy
      have high' (b : Bool) : F (Function.update y v b) = true := by
        apply (on _).mpr;refine ⟨_,mem,?_⟩
        rw [show (W pre (Function.update y v b)).getD w false = (Function.update y v b) u from vl_input _ _ _ u.isLt,
          Function.update_of_ne (show u ≠ v from fun e => ne (congrArg Fin.val e)),yu]
      exact (high' false).trans (high' true).symm
    · apply impossible_mask (centers S) (piv v hv)
      have high' (b : Bool) : F (Function.update (centers S) v b) = true := by
        apply (on _).mpr;refine ⟨_,mem,?_⟩
        apply monotone_off S pre preops avoid _ _ (by simp) _ w special yes
        apply initial_le
        intro i outside _
        have iv : i ≠ v := fun eq => outside (eq ▸ hv)
        simp [centers,Function.update_of_ne iv,outside]
      exact (high' false).trans (high' true).symm

end PEqualNP.Research.Dominating3321

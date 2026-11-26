import PEqualNP.Research.L_meta_2584_incidence

namespace PEqualNP.Research.ReadEnvelope
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Research.ReadTwoBudget PEqualNP.Research.ReadTwoIncidence

abbrev Bill := Nat × Nat

/-- Simultaneous upper bounds for the occurrences of the two designated inputs in any parse. -/
def billStep (W : List Bill) (g : Gate) : Bill :=
  let a := W.getD (g.inputs.getD 0 0) (0,0)
  let b := W.getD (g.inputs.getD 1 0) (0,0)
  match g.op with
  | .and => (a.1+b.1,a.2+b.2)
  | .or => (max a.1 b.1,max a.2 b.2)
  | _ => (0,0)
def rawBill (a b i : Nat) : Bill := (if i=a then 1 else 0,if i=b then 1 else 0)
def bills (C : Circuit) (n a b : Nat) :=
  C.gates.foldl (fun W g => W ++ [billStep W g]) ((List.range n).map (rawBill a b))

def Valid (c : Bill) (v : Bool) (f : State) : Prop :=
  ∀ i j : Fin 3, c.1 ≤ i.val → c.2 ≤ j.val → v = true → f i j = true

theorem valid_add {c d : Bill} {v w f h} (a : Valid c v f) (b : Valid d w h) :
    Valid (max c.1 d.1,max c.2 d.2) (v || w) (add f h) := by
  intro i j ci cj yes
  rcases Bool.or_eq_true_iff.mp yes with l | r
  · simp [add,a i j ((Nat.le_max_left ..).trans ci) ((Nat.le_max_left ..).trans cj) l]
  · simp [add,b i j ((Nat.le_max_right ..).trans ci) ((Nat.le_max_right ..).trans cj) r]

theorem valid_mul {c d : Bill} {v w f h} (a : Valid c v f) (b : Valid d w h) :
    Valid (c.1+d.1,c.2+d.2) (v && w) (mul f h) := by
  intro i j ci cj yes
  change c.1+d.1 ≤ i.val at ci
  change c.2+d.2 ≤ j.val at cj
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp yes
  apply decide_eq_true
  exact ⟨⟨c.1,by omega⟩,⟨c.2,by omega⟩,⟨d.1,by omega⟩,⟨d.2,by omega⟩,ci,cj,a _ _ le_rfl le_rfl l,b _ _ le_rfl le_rfl r⟩

def pairBits (a b i : Nat) : Bool := decide (i=a ∨ i=b)
theorem raw_valid (a b i : Nat) (ne : a≠b) : Valid (rawBill a b i) (pairBits a b i)
    (encode (leafVectors [a,b] 2 i)) := by
  intro u v hu hv h
  rcases (of_decide_eq_true h : i=a ∨ i=b) with rfl|rfl <;>
    simp_all [rawBill,encode,leafVectors,fits,List.getD,Ne.symm ne]

private def evStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem propagate (gs : List Gate) (allowed : ∀ g∈gs,g.op = .and ∨ g.op = .or)
    (two : ∀ g∈gs,g.inputs.length=2) (W : List Bill) (V : List Bool) (F : List State)
    (wv : W.length=V.length) (wf : W.length=F.length)
    (ok : ∀ i, Valid (W.getD i (0,0)) (V.getD i false) (F.getD i zero)) :
    ∀ i, Valid ((gs.foldl (fun w g => w ++ [billStep w g]) W).getD i (0,0))
    ((gs.foldl evStep V).getD i false)
    ((gs.foldl (fun f g => f ++ [fastStep f g]) F).getD i zero) := by
  induction gs generalizing W V F with
  | nil => exact ok
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun t h => allowed t (List.mem_cons_of_mem _ h)) (fun t h => two t (List.mem_cons_of_mem _ h))
      _ _ _ (by simp [evStep,wv]) (by simp [wf])
    intro i
    unfold evStep
    by_cases lo : i < W.length
    · rw [List.getD_append _ _ _ _ lo,List.getD_append _ _ _ _ (wv ▸ lo),List.getD_append _ _ _ _ (wf ▸ lo)]
      exact ok i
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),←wv,←wf]
      cases eq : i-W.length with
      | succ j => simp [List.getD,Valid]
      | zero =>
        obtain ⟨a,b,h⟩ := List.length_eq_two.mp (two g List.mem_cons_self)
        rcases allowed g List.mem_cons_self with op|op <;>
          simp only [billStep,fastStep,h,op,List.getD_cons_zero,List.getD_cons_succ,List.map_cons,List.map_nil,
            GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,Bool.and_true,Bool.or_false,id_eq]
        · exact valid_mul (ok a) (ok b)
        · exact valid_add (ok a) (ok b)

theorem pair_ok (C : Circuit) (n a b : Nat) (ne : a ≠ b) (ao : IsAO2 n C) :
    Valid ((bills C n a b).getD C.output (0,0)) (C.eval ((List.range n).map (pairBits a b)))
      ((fastWires C n a b).getD C.output zero) := by
  apply propagate C.gates ao.1 ao.2.2 _ _ _ (by simp) (by simp) _ C.output
  intro i
  by_cases hi : i<n
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_range hi] using raw_valid a b i ne
  · have hn : (List.range n)[i]? = none := List.getElem?_eq_none (by simp; omega)
    simp [List.getD_eq_getElem?_getD,hn,Valid]

theorem normalize_by_bills {P L} (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (ao : IsAO2 (P+L) C) (correct : ∀ z, circuitFun (P+L) C z = incidence I z)
    (bound : ∀ p l, I p l →
      let v := (bills C (P+L) p.val (P+l.val)).getD C.output (0,0)
      v.1 ≤ 2 ∧ v.2 ≤ 2) : IsReadK (P+L) C 2 := by
  apply (read2_iff_edges I C ao correct).mpr
  intro p l edge
  let x : Fin (P+L) → Bool := fun i => pairBits p.val (P+l.val) i.val
  have eq : List.ofFn x = (List.range (P+L)).map (pairBits p.val (P+l.val)) := by
    apply List.ext_getElem <;> simp [x]
  have hit : circuitFun (P+L) C x = true := by
    rw [correct]
    apply decide_eq_true
    exact ⟨p,l,edge,by simp [x,pairBits],by simp [x,pairBits]⟩
  change C.eval (List.ofFn x) = true at hit
  rw [eq] at hit
  exact pair_ok C _ _ _ (by have := p.isLt; omega) ao 2 2 (bound p l edge).1 (bound p l edge).2 hit

end PEqualNP.Research.ReadEnvelope

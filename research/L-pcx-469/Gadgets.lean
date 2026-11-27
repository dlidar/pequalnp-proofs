import Machine
namespace SpinCircuit
open PEqualNP.CircuitLowerBounds
variable {X : Type}
theorem indexed {n B l : ℕ} {base : X → List Bool} (fs : Fin l → X → Bool)
    (hf : ∀ i, built n base (fs i) B) (M : ℕ) (hm : n ≤ M) :
    ∃ (p : List Gate) (o : Fin l → ℕ), legal M p ∧ p.length ≤ l*B ∧
    (∀ i, o i < M+p.length) ∧ ∀ x w, w.length=M → base x <+: w →
    ∀ i, (run p w).getD (o i) false = fs i x := by
  obtain ⟨p,os,hp,hl,hos,hob,hev⟩ := many base (List.ofFn fs)
    (fun f h => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h;exact hf i) M hm
  simp only [List.length_ofFn] at hl hos
  let o := fun i : Fin l => os[i.val]'(hos.symm ▸ i.isLt)
  refine ⟨p,o,hp,hl,fun i => hob _ (List.getElem_mem ..),?_⟩
  intro x w hw hh i
  have h := congrArg (fun s : List Bool => s[i.val]?) (hev x w hw hh)
  have hi : i.val < os.length := by rw [hos];exact i.isLt
  simpa [List.getElem?_map,List.getElem?_eq_getElem hi,i.isLt,o] using h

def cell (M u v z : ℕ) : List Gate := [⟨.and,[u,v]⟩,⟨.or,[z,M]⟩]
theorem cell_legal {M u v z : ℕ} (hu : u < M) (hv : v < M) (hz : z < M) : legal M (cell M u v z) := by
  intro j hj
  have hl : j < 2 := hj
  interval_cases j <;> simp [cell,allowed] <;> omega
theorem cell_eval {M u v z : ℕ} (w : List Bool) (hw : w.length=M) (hz : z<M) :
    (run (cell M u v z) w).getD (M+1) false = (w.getD z false || (w.getD u false && w.getD v false)) := by
  subst M
  have h (ts : List Bool) : (w ++ ts)[z]?.getD false = w[z]?.getD false := by rw [List.getElem?_append_left hz]
  simp [run,cell,GateOp.eval,h,List.getD_eq_getElem?_getD]

def valAt (w : List Bool) (i : ℕ) := w.getD i false
theorem cell_built {n : ℕ} {base : X → List Bool} (len : ∀ x, (base x).length=n)
    (u v z : Fin n) :
    built n base (fun x => (base x).getD z false || ((base x).getD u false && (base x).getD v false)) 2 := by
  intro M hM
  refine ⟨cell M u v z,M+1,cell_legal (u.isLt.trans_le hM) (v.isLt.trans_le hM) (z.isLt.trans_le hM),by rfl,by change M+1<M+2;omega,?_⟩
  intro x w hw h
  rw [cell_eval w hw (z.isLt.trans_le hM)]
  obtain ⟨v',rfl⟩ := h
  simp only [List.getD_append _ _ _ _ (show z.val < (base x).length by rw [len];exact z.isLt),
    List.getD_append _ _ _ _ (show u.val < (base x).length by rw [len];exact u.isLt),
    List.getD_append _ _ _ _ (show v.val < (base x).length by rw [len];exact v.isLt)]

def ones (fs : List ℕ) (w : List Bool) := (fs.map (fun i => w.getD i false)).count true

theorem unary (n D : ℕ) (hn : 2 ≤ n) (ids : List ℕ) (hi : ∀ i ∈ ids, i < n) :
    ∃ (p : List Gate) (o : Fin (D+1) → ℕ), legal n p ∧ p.length ≤ ids.length*((D+1)*2) ∧
    (∀ j, o j < n+p.length) ∧ ∀ w : List Bool, w.length=n → w.getD 0 false=false → w.getD 1 false=true →
    ∀ j : Fin (D+1), (run p w).getD (o j) false = decide (j.val ≤ ones ids w) := by
  induction ids with
  | nil =>
    refine ⟨[],fun j => if j.val=0 then 1 else 0,by intro j h;simp at h,by simp,?_,?_⟩
    · intro j; dsimp only; split <;> simp <;> omega
    · intro w hw h0 h1 j
      by_cases hj : j.val=0 <;> simp [run,ones,hj] <;> assumption
  | cons u us ih =>
    obtain ⟨p,o,hp,hl,ho,he⟩ := ih (fun i h => hi i (List.mem_cons_of_mem _ h))
    let M := n+p.length
    let B := {w : List Bool // w.length=M}
    let b : B → List Bool := Subtype.val
    let prev (j : Fin (D+1)) : Fin (D+1) := ⟨j.val-1,by omega⟩
    let fs := fun (j : Fin (D+1)) (w : B) =>
      w.val.getD (o j) false || (w.val.getD u false && w.val.getD (o (prev j)) false)
    have hu := hi u List.mem_cons_self
    have hb (j) : built M b (fs j) 2 :=
      cell_built (fun w : B => w.property) ⟨u,by dsimp [M];omega⟩ ⟨o (prev j),ho _⟩ ⟨o j,ho j⟩
    obtain ⟨q,z,hq,hlq,hz,hev⟩ := indexed fs hb M le_rfl
    refine ⟨p++q,z,legal_append hp hq,?_,fun j => by simpa [M,Nat.add_assoc] using hz j,?_⟩
    · simp only [List.length_append,List.length_cons]
      exact (Nat.add_le_add hl hlq).trans_eq (by ring)
    · intro w hw h0 h1 j
      have hlen : (run p w).length=M := by rw [run_length,hw]
      rw [run_append,hev ⟨run p w,hlen⟩ (run p w) hlen (by rfl) j]
      change ((run p w).getD (o j) false || ((run p w).getD u false && (run p w).getD (o (prev j)) false)) = _
      rw [he w hw h0 h1 j,he w hw h0 h1 (prev j),old_wire p (hw ▸ hu)]
      change (_ || (_ && decide (j.val-1 ≤ ones us w))) = _
      cases hbit : w.getD u false <;> simp [ones,List.count_cons,List.getD_eq_getElem?_getD] at hbit ⊢ <;> simp_all <;> omega

end SpinCircuit

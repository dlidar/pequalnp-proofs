import Mathlib
import PEqualNP.Defs.NestedCoverCircuit
namespace SpinCircuit
open PEqualNP.CircuitLowerBounds
def allowed (g : Gate) : Prop := ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)
def legal (n : ℕ) (p : List Gate) : Prop :=
  ∀ j (h : j < p.length), allowed p[j] ∧ ∀ i ∈ p[j].inputs, i < n+j
def run (p : List Gate) (w : List Bool) := p.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w
theorem run_append (p q : List Gate) (w : List Bool) : run (p++q) w = run q (run p w) := List.foldl_append ..
theorem extends_run (p : List Gate) (w : List Bool) : w <+: run p w := by
  induction p generalizing w with
  | nil => rfl
  | cons g p ih => exact (List.prefix_append w _).trans (ih _)
theorem run_length (p : List Gate) (w : List Bool) : (run p w).length = w.length+p.length := by
  induction p generalizing w with
  | nil => simp [run]
  | cons g p ih => change (run p (w ++ [_])).length = _; rw [ih]; simp; omega
theorem old_wire (p : List Gate) {w : List Bool} {i : ℕ} (h : i < w.length) :
    (run p w).getD i false = w.getD i false := by
  obtain ⟨q,hq⟩ := extends_run p w
  rw [← hq,List.getD_append _ _ _ _ h]
theorem legal_append {n : ℕ} {p q : List Gate} (hp : legal n p) (hq : legal (n+p.length) q) : legal n (p++q) := by
  intro j hj
  by_cases h : j < p.length
  · simpa only [List.getElem_append_left h] using hp j h
  · have hj' : j-p.length < q.length := by simp at hj;omega
    rw [List.getElem_append_right (by omega)]
    have hh := hq _ hj'
    refine ⟨hh.1,fun i hi => ?_⟩
    have := hh.2 i hi;omega

theorem circuit_legal {n : ℕ} {p : List Gate} (hp : legal n p) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨p,0⟩ ∧ ∀ a ∈ p, allowed a := by
  constructor
  · intro j hj i hi
    apply (hp j hj).2 i
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi
  · intro a ha
    obtain ⟨j,h,hj⟩ := List.getElem_of_mem ha
    exact hj ▸ (hp j h).1

variable {X : Type}
def built (n : ℕ) (base : X → List Bool) (f : X → Bool) (B : ℕ) : Prop :=
  ∀ M, n ≤ M → ∃ (p : List Gate) (o : ℕ), legal M p ∧ p.length ≤ B ∧ o < M+p.length ∧
  ∀ x w, w.length=M → base x <+: w → (run p w).getD o false = f x

theorem weaken {n B C : ℕ} {base : X → List Bool} {f : X → Bool} (h : built n base f B) (hh : B ≤ C) :
    built n base f C := by
  intro M hm
  obtain ⟨p,o,hp,hl,ho,he⟩ := h M hm
  exact ⟨p,o,hp,hl.trans hh,ho,he⟩

theorem read_input {n : ℕ} (base : X → List Bool) (hlen : ∀ x, (base x).length = n) (i : Fin n) :
    built n base (fun x => (base x).getD i false) 0 := by
  intro M hM
  refine ⟨[],i,by intro j h; simp at h,by simp,by simpa using i.isLt.trans_le hM,?_⟩
  intro x w hw h
  obtain ⟨v,rfl⟩ := h
  exact List.getD_append _ _ _ _ (by rw [hlen];exact i.isLt)

theorem many {n B : ℕ} (base : X → List Bool) (fs : List (X → Bool))
    (hf : ∀ f ∈ fs, built n base f B) (M : ℕ) (hm : n ≤ M) :
    ∃ (p : List Gate) (os : List ℕ), legal M p ∧ p.length ≤ fs.length*B ∧ os.length=fs.length ∧
    (∀ o ∈ os, o < M+p.length) ∧ ∀ x w, w.length=M → base x <+: w →
    (os.map fun o => (run p w).getD o false) = fs.map (fun f => f x) := by
  induction fs generalizing M with
  | nil => exact ⟨[],[],by intro j h; simp at h,by simp,rfl,by simp,by simp⟩
  | cons f fs ih =>
    obtain ⟨p,o,hp,hl,ho,he⟩ := hf f List.mem_cons_self M hm
    obtain ⟨q,os,hq,hql,hos,hob,hev⟩ := ih (fun f h => hf f (List.mem_cons_of_mem _ h)) (M+p.length) (by omega)
    refine ⟨p++q,o::os,legal_append hp hq,?_,by simp [hos],?_,?_⟩
    · simp [Nat.add_mul];omega
    · intro j hj
      rcases List.mem_cons.mp hj with rfl|hj
      · simp;omega
      · simpa [Nat.add_assoc] using hob j hj
    · intro x w hw hh
      have ww : (run p w).length=M+p.length := by rw [run_length,hw]
      simp only [run_append,List.map_cons,old_wire q (ww ▸ ho),he x w hw hh,
        hev x (run p w) ww (hh.trans (extends_run p w))]

end SpinCircuit

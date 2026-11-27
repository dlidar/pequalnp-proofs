import Mathlib
import PEqualNP.Defs.Represents

namespace Mask114591Support
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def ancestors (n : Nat) (gs : List Gate) (s : Finset Nat) : Finset Nat :=
  match gs with
  | [] => s
  | g :: tail =>
    let r := ancestors (n+1) tail s
    if n ∈ r then r.erase n ∪ g.inputs.toFinset else r

theorem ancestor_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (n : Nat) (s : Finset Nat) : (ancestors n gs s).card ≤ s.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [ancestors]
  | cons g gs ih =>
    have hi := ih (fun a ha => h a (.tail _ ha)) (n+1)
    have hg := h g (.head _)
    let r := ancestors (n+1) gs s
    change (if n ∈ r then r.erase n ∪ g.inputs.toFinset else r).card ≤ _
    split
    next hm =>
      have hu := Finset.card_union_le (r.erase n) g.inputs.toFinset
      have hc := Finset.card_erase_add_one hm
      have hl := List.toFinset_card_le g.inputs
      change r.card ≤ _ at hi
      simp only [List.length_cons]
      omega
    next => simp only [List.length_cons]; exact hi.trans (by omega)

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def agrees (a b : List Bool) (s : Finset Nat) :=
  ∀ i ∈ s, a.getD i false = true → b.getD i false = true

theorem append_bit (w : List Bool) (v : Bool) (i : Nat) :
    (w++[v]).getD i false = if i = w.length then v else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> simp [List.getD]
  | cons a w ih =>
    cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD] using ih i

theorem increases (g : Gate) (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (a b : List Bool) (h : agrees a b g.inputs.toFinset) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hOp | hOp
  · rw [hOp]; simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ha i hi
    exact h i (List.mem_toFinset.mpr hi) (ha i hi)
  · change g.op = GateOp.or at hOp
    rw [hOp]; simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hv⟩
    exact ⟨i,hi,h i (List.mem_toFinset.mpr hi) hv⟩

theorem propagate (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (a b : List Bool) (len : a.length = b.length) (s : Finset Nat)
    (h : agrees a b (ancestors a.length gs s)) :
    agrees (gs.foldl step a) (gs.foldl step b) s := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun u hu => hg u (.tail _ hu)) (step a g) (step b g) (by simp [step,len])
    let r := ancestors (a.length+1) gs s
    change agrees a b (if a.length ∈ r then r.erase a.length ∪ g.inputs.toFinset else r) at h
    intro i hi
    change i ∈ ancestors (step a g).length gs s at hi
    simp only [step,List.length_append,List.length_singleton] at hi
    change i ∈ r at hi
    simp only [step,append_bit,← len]
    by_cases eq : i = a.length
    · subst i
      simp only [if_pos rfl]
      rw [if_pos hi] at h
      apply increases g (hg g (.head _))
      exact fun j hj => h j (Finset.mem_union_right _ hj)
    · simp only [if_neg eq]
      apply h i
      by_cases hm : a.length ∈ r
      · rw [if_pos hm]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩)
      · simpa [hm] using hi

theorem monotone_support (C : Circuit) (hc : Monotone2 C) (n : Nat) :
    ∃ s : Finset Nat, s.card ≤ C.size+1 ∧ ∀ a b : List Bool,
      a.length = n → b.length = n → agrees a b s → C.eval a = true → C.eval b = true := by
  refine ⟨ancestors n C.gates {C.output}, ?_, ?_⟩
  · simpa [Circuit.size,Nat.add_comm] using ancestor_bound C.gates (fun g hg => (hc g hg).2) n {C.output}
  · intro a b ha hb h
    subst n
    exact propagate C.gates (fun g hg => (hc g hg).1) a b hb.symm {C.output} h C.output (by simp)
end Mask114591Support
#print axioms Mask114591Support.monotone_support

import PEqualNP.Research.ReadEnvelope
import PEqualNP.Outside.L_meta_17442

namespace PEqualNP.Research.PureReadTwo
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Research.ReadEnvelope PEqualNP.Research.ReadTwoIncidence

def Fits (v : Bill) (k : Nat) := v.1 ≤ k ∧ v.2 ≤ k
def cap (S : Finset Nat) (i : Nat) := if i ∈ S then 1 else 2
def Rule (S : Finset Nat) (i : Nat) (g : Gate) :=
  (i ∈ S → g.op = .or ∧ ∀ t ∈ g.inputs, t ∈ S) ∧
  (g.op = .and → ∀ t ∈ g.inputs, t ∈ S)

theorem extend (S : Finset Nat) (W : List Bill) (x : Bill)
    (old : ∀ i, Fits (W.getD i (0,0)) (cap S i)) (hx : Fits x (cap S W.length)) :
    ∀ i, Fits ((W ++ [x]).getD i (0,0)) (cap S i) := by
  intro i
  by_cases hi : i < W.length
  · rw [List.getD_append _ _ _ _ hi]; exact old i
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    cases e : i-W.length with
    | zero => simpa [show i=W.length by omega] using hx
    | succ j => simp [List.getD,Fits]

theorem step {S W g} (rule : Rule S (List.length W) g) (two : g.inputs.length=2)
    (old : ∀ i, Fits (List.getD W i (0,0)) (cap S i)) :
    Fits (billStep W g) (cap S W.length) := by
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp two
  have one : ∀ t ∈ S, Fits (W.getD t (0,0)) 1 := fun t h => by simpa [cap,h] using old t
  have both : ∀ t, Fits (W.getD t (0,0)) 2 := by
    intro t; have h := old t; unfold cap at h; split at h <;> unfold Fits at * <;> omega
  by_cases pure : W.length ∈ S
  · obtain ⟨op,src⟩ := rule.1 pure
    have ha := one a (src a (by simp [ab]))
    have hb := one b (src b (by simp [ab]))
    simpa [billStep,ab,op,cap,pure,Fits,Nat.max_le] using
      (show ((W.getD a (0,0)).1 ≤ 1 ∧ (W.getD b (0,0)).1 ≤ 1) ∧
        ((W.getD a (0,0)).2 ≤ 1 ∧ (W.getD b (0,0)).2 ≤ 1) from ⟨⟨ha.1,hb.1⟩,ha.2,hb.2⟩)
  · cases op : g.op <;> simp [billStep,op,ab,cap,pure,Fits,Nat.max_le]
    all_goals first
      | exact ⟨⟨(both a).1,(both b).1⟩,(both a).2,(both b).2⟩
      | have ha := one a (rule.2 op a (by simp [ab]))
        have hb := one b (rule.2 op b (by simp [ab]))
        simp only [Fits,List.getD_eq_getElem?_getD] at ha hb
        omega

theorem run (S : Finset Nat) (gs : List Gate) (W : List Bill)
    (rules : ∀ j (hj:j<gs.length), Rule S (W.length+j) gs[j])
    (two : ∀ g∈gs,g.inputs.length=2)
    (old : ∀ i, Fits (W.getD i (0,0)) (cap S i)) :
    ∀ i, Fits ((gs.foldl (fun w g => w ++ [billStep w g]) W).getD i (0,0)) (cap S i) := by
  induction gs generalizing W with
  | nil => exact old
  | cons g gs ih =>
    apply ih
    · intro j hj
      have h := rules (j+1) (by simp;omega)
      change Rule S (W.length+(j+1)) gs[j] at h
      simpa [Nat.add_assoc,Nat.add_comm 1 j] using h
    · exact fun g h => two g (List.mem_cons_of_mem _ h)
    · exact extend S W _ old (step (by have h := rules 0 (by simp); change Rule S (W.length+0) g at h; exact h) (two _ List.mem_cons_self) old)

theorem by_topology {P L} (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (ao : IsAO2 (P+L) C) (correct : ∀ z, circuitFun (P+L) C z = incidence I z)
    (S : Finset Nat) (rules : ∀ j (hj:j<C.gates.length), Rule S (P+L+j) C.gates[j]) :
    IsReadK (P+L) C 2 := by
  apply normalize_by_bills I C ao correct
  intro p l _
  have h := run S C.gates ((List.range (P+L)).map (rawBill p.val (P+l.val))) (by simpa using rules)
    ao.2.2 (by
      intro i
      by_cases hi : i<P+L
      · simp [List.getD_eq_getElem?_getD,List.getElem?_range hi,rawBill,Fits,cap]
        split <;> split <;> split <;> decide
      · have hn : (List.range (P+L))[i]? = none := List.getElem?_eq_none (by simp;omega)
        simp [List.getD_eq_getElem?_getD,hn,Fits]) C.output
  change Fits _ 2
  unfold bills
  unfold cap at h
  split at h <;> unfold Fits at * <;> omega

end PEqualNP.Research.PureReadTwo

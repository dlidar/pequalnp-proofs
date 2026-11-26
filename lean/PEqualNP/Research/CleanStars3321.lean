import PEqualNP.Outside.L_meta_17442

namespace PEqualNP.Research.CleanStars3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17442
open Evaluation

def off (w : List Bool) : List Gate → Prop
  | [] => True
  | g :: tail => (g.op = .and → g.op.eval (g.inputs.map fun i => w.getD i false) = false) ∧ off (step w g) tail

theorem off_append (w : List Bool) (a b : List Gate) :
    off w (a ++ b) ↔ off w a ∧ off (a.foldl step w) b := by
  induction a generalizing w with
  | nil => simp [off]
  | cons g gs ih => simp only [List.cons_append,off,List.foldl_cons,ih,and_assoc]

theorem off_ors (gs : List Gate) (h : ∀ g ∈ gs, g.op = .or) (w : List Bool) : off w gs := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨fun e => ?_,ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) _⟩
    have := h g List.mem_cons_self
    simp_all

theorem fold_low (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step];omega)]
    exact List.getD_append _ _ _ _ hi

theorem off_at (gs : List Gate) (w : List Bool) (h : off w gs)
    (j : Nat) (g : Gate) (hj : gs[j]? = some g) (op : g.op = .and) :
    (gs.foldl step w).getD (w.length+j) false = false := by
  induction gs generalizing j w with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero =>
      have eq : k = g := by simpa using hj
      subst g
      rw [List.foldl_cons,Nat.add_zero,fold_low ks _ (by simp [step])]
      simp [step]
      exact h.1 op
    | succ j =>
      have hh := ih (step w k) h.2 j (by simpa using hj)
      simpa [step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem block_off (w : List Bool) (a t v : Nat) (rest : List Nat) (lead : Bool)
    (ht : t < w.length) (hv : v < w.length) (hr : ∀ r ∈ rest, r < w.length)
    (miss : (w.getD t false && (v::rest).any fun r => w.getD r false) = false) :
    off w (blockGates w.length a t v rest lead) := by
  unfold blockGates
  apply (off_append ..).mpr
  constructor
  · apply off_ors
    intro g hg
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
    rfl
  · rw [chain_run w v rest hv hr _ le_rfl]
    constructor
    · intro _
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true]
      rw [acc_low _ _ _ _ _ ht, acc_chain _ _ _ _ hv le_rfl]
      simpa [part] using miss
    · cases lead <;> simp [off]

theorem cover_off (n : Nat) (own : List (Nat × List Nat))
    (valid : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (w : List Bool) (hw : n ≤ w.length) (a : Nat) (lead : Bool)
    (ha : lead = false → a < w.length) (miss : hit w own = false) :
    off w (coverGatesB w.length lead a own) := by
  induction own generalizing w a lead with
  | nil => trivial
  | cons o os ih =>
    have tail := fun o ho => valid o (List.mem_cons_of_mem _ ho)
    obtain ⟨t,l⟩ := o
    have both : (w.getD t false && l.any (fun r => w.getD r false)) = false ∧ hit w os = false := by
      simpa [hit] using miss
    cases l with
    | nil => exact ih tail w hw a lead ha both.2
    | cons v rest =>
      have hb := valid (t,v::rest) List.mem_cons_self
      have ht : t < w.length := lt_of_lt_of_le hb.1 hw
      have hvs : ∀ r ∈ v::rest, r < w.length := fun r hr => lt_of_lt_of_le (hb.2 r hr) hw
      have hv := hvs v List.mem_cons_self
      have hr := fun r h => hvs r (List.mem_cons_of_mem _ h)
      obtain ⟨len,low,_⟩ := block_run w a t v rest lead ha ht hv hr
      rw [coverGatesB,off_append]
      refine ⟨block_off w a t v rest lead ht hv hr both.1,?_⟩
      let bg := blockGates w.length a t v rest lead
      have hpos : 0 < bg.length := by dsimp [bg];rw [block_length];omega
      have tall : (bg.foldl step w).length = w.length+bg.length := len
      have hm : hit (bg.foldl step w) os = false :=
        (hit_congr _ w n os (fun i hi => low i (lt_of_lt_of_le hi hw)) tail).trans both.2
      have z := ih tail (bg.foldl step w) (by omega) (w.length+bg.length-1) false (by omega) hm
      rw [tall] at z
      exact z

theorem no_and_on_reject (n : Nat) (own : List (Nat × List Nat))
    (valid : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) (nonempty : ∀ o ∈ own, o.2 ≠ [])
    (x : Fin n → Bool) (miss : circuitFun n (coverCircuitB n own) x = false)
    (j : Nat) (hj : j < (coverCircuitB n own).gates.length)
    (op : (NestedCover.gateAt (coverCircuitB n own) j).op = .and) :
    ((coverCircuitB n own).wires (List.ofFn x)).getD (n+j) false = false := by
  let D := coverCircuitB n own
  have hm : hit (List.ofFn x) own = false := by
    rw [← (cover_all n own valid nonempty).2 _ (by simp)]
    exact miss
  have offg : off (List.ofFn x) D.gates := by
    rw [Topology.Helpers.gates_eq]
    simpa using cover_off n own valid (List.ofFn x) (by simp) 0 true (by simp) hm
  have result := off_at D.gates (List.ofFn x) offg j _ (Topology.Helpers.gateAt_get D j hj) op
  change (D.gates.foldl step (List.ofFn x)).getD (n+j) false = false
  simpa only [List.length_ofFn] using result

end PEqualNP.Research.CleanStars3321

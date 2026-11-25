import PEqualNP.Research.L_meta_11718_circuits
import PEqualNP.Research.L_meta_11718_graph

namespace PEqualNP.Research.SevenVertexBudget
open PEqualNP.CircuitLowerBounds PEqualNP.Research.SingleInverter
open PEqualNP.Research.InverterCircuit PEqualNP.Research.SevenVertexInverter

def reads (g : Gate) : List ℕ := match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def cost (g : Gate) : ℕ := match g.op with
  | .not => 0
  | _ => 1

theorem arity (g : Gate) (h : g.inputs.length ≤ 2) : (reads g).length ≤ cost g + 1 := by
  rcases g with ⟨op,args⟩
  cases op <;> simp_all [reads,cost,List.length_take]

theorem effective (g : Gate) (w : List Bool) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) =
    g.op.eval ((reads g).map (fun i => w.getD i false)) := by
  rcases g with ⟨op,args⟩
  cases op <;> try rfl
  cases args <;> rfl

-- Weighted form of the backward support argument from upstream L_meta_1942.
theorem weighted_support (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + (gs.map cost).sum ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ (reads g).toFinset else F
    have hb : B.card ≤ F.card + cost g := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) (reads g).toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le (reads g)).trans (arity g (hg g (by simp)))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left (reads g).toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      rw [effective g (run gs x),effective g (run gs y)]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


theorem essential : ∀ i : Fin 7, ∃ x y : Fin 7 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ target x ≠ target y := by decide +kernel

theorem six_binary (C : Circuit) (h : candidate C) : 6 ≤ (C.gates.map cost).sum := by
  obtain ⟨S,bound,dep⟩ := weighted_support 7 C.gates (fun g hg => (h.1 g hg).2) {C.output}
  have cover : Finset.range 7 ⊆ S := by
    intro i hi
    by_contra missing
    have hin := Finset.mem_range.mp hi
    obtain ⟨x,y,same,diff⟩ := essential ⟨i,hin⟩
    apply diff
    rw [←h.2.2 x,←h.2.2 y]
    apply dep (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro j hj
    by_cases hjn : j < 7
    · rw [List.getD_eq_getElem _ _ (by simpa using hjn),List.getD_eq_getElem _ _ (by simpa using hjn)]
      simp only [List.getElem_ofFn]
      apply same
      intro e
      have sameIndex : j = i := congrArg Fin.val e
      exact missing (sameIndex ▸ hj)
    · simp [Nat.le_of_not_lt hjn]
  have := Finset.card_le_card cover
  simp only [Finset.card_range] at this
  simp only [Finset.card_singleton] at bound
  omega

theorem cost_le (gs : List Gate) : (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have cg : cost g ≤ 1 := by cases g with | mk op args => cases op <;> simp [cost]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem cost_lt (gs : List Gate) (used : ∃ g ∈ gs, g.op = .not) : (gs.map cost).sum < gs.length := by
  induction gs with
  | nil => simp at used
  | cons g gs ih =>
    obtain ⟨a,ha,hn⟩ := used
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rcases List.mem_cons.mp ha with e | hg
    · subst a
      have z : cost g = 0 := by simp [cost,hn]
      have := cost_le gs
      omega
    · have := ih ⟨a,hg,hn⟩
      have c := cost_le [g]
      simp at c
      omega

theorem gate_window (C : Circuit) (h : candidate C) (unreplaced : ¬ replacement C) :
    7 ≤ C.gates.length ∧ C.gates.length ≤ 10 := by
  have used : ∃ g ∈ C.gates, g.op = .not := by
    by_contra no
    apply unreplaced
    refine ⟨C.gates,C.output,?_,le_rfl,h.2.2⟩
    intro g hg
    obtain ⟨op,sz⟩ := h.1 g hg
    refine ⟨?_,sz⟩
    rcases op with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (no ⟨g,hg,hn⟩).elim
  have upper : ¬ 11 ≤ C.gates.length := fun e =>
    unreplaced ⟨reference.gates,reference.output,reference_legal, reference_size ▸ e,reference_correct⟩
  have := cost_lt C.gates used
  have := six_binary C h
  omega

end PEqualNP.Research.SevenVertexBudget

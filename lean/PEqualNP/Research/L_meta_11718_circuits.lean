import PEqualNP.Research.L_meta_11718_boundary
import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

namespace PEqualNP.Research.InverterCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.Research.SingleInverter

def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

def binaryMono (gs : List Gate) := ∀ g ∈ gs, g.op = .and ∨ g.op = .or

theorem read_order {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) (i : ℕ) :
    u.getD i false ≤ v.getD i false := by
  have hl := h.length_eq
  by_cases hi : i < u.length
  · have hj : i < v.length := hl ▸ hi
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
    exact h.get hi hj
  · simp only [List.getD_eq_default _ _ (by omega : u.length ≤ i),
      List.getD_eq_default _ _ (by omega : v.length ≤ i),le_refl]

theorem run_order {gs : List Gate} (ok : binaryMono gs) {u v : List Bool}
    (h : List.Forall₂ (· ≤ ·) u v) : List.Forall₂ (· ≤ ·) (run gs u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun t ht => ok t (List.mem_cons_of_mem g ht))
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    rcases ok g List.mem_cons_self with e | e
    · simp only [e,GateOp.eval,Bool.le_iff_imp,List.all_eq_true,List.mem_map,id_eq]
      rintro all b ⟨i, hi, hb⟩
      rw [← hb]
      exact Bool.le_iff_imp.mp (read_order h i) (all _ ⟨i,hi,rfl⟩)
    · simp only [e,GateOp.eval,Bool.le_iff_imp,List.any_eq_true,List.mem_map,id_eq]
      rintro ⟨_,⟨i,hi,rfl⟩,ht⟩
      exact ⟨_,⟨i,hi,rfl⟩,Bool.le_iff_imp.mp (read_order h i) ht⟩

def input {n : ℕ} (x : Row (Fin n)) : List Bool := List.ofFn (fun i => decide (i ∈ x))

theorem input_order {n : ℕ} {x y : Row (Fin n)} (h : x ⊆ y) :
    List.Forall₂ (· ≤ ·) (input x) (input y) := by
  apply List.forall₂_of_length_eq_of_get (by simp [input])
  intro i hi hj
  simpa [input,List.get_eq_getElem,Bool.le_iff_imp] using
    (show (⟨i,by simpa [input] using hi⟩ : Fin n) ∈ x → _ from fun hx => h hx)

def signal (pre : List Gate) (args : List ℕ) {n : ℕ} (x : Row (Fin n)) : Bool :=
  (args.map (fun i => (run pre (input x)).getD i false)).headD false

def out (pre post : List Gate) (args : List ℕ) (o : ℕ) {n : ℕ} (x : Row (Fin n)) : Bool :=
  (Circuit.mk (pre ++ (⟨.not,args⟩ :: post)) o).eval (input x)

theorem signal_mono {pre : List Gate} (h : binaryMono pre) (args : List ℕ) (n : ℕ) :
    Monotone (signal (n := n) pre args) := by
  intro x y hxy
  cases args with
  | nil => exact le_rfl
  | cons a _ => exact read_order (run_order h (input_order hxy)) a

theorem circuit_on_slice {pre post : List Gate} (hp : binaryMono pre) (ht : binaryMono post)
    (args : List ℕ) (o n : ℕ) : OnSlice (signal (n := n) pre args) (out pre post args o) := by
  intro x y hxy he
  apply Bool.le_iff_imp.mp
  unfold out Circuit.eval Circuit.wires
  rw [List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_cons]
  apply read_order (run_order ht ?_)
  apply List.rel_append (run_order hp (input_order hxy))
  apply List.Forall₂.cons _ List.Forall₂.nil
  change (!signal pre args x) ≤ (!signal pre args y)
  rw [he]

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run,Circuit.wires,List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run,Circuit.wires]
  | append_singleton _ _ ih => simp [run_snoc,ih]; omega

-- Backward support argument adapted from the checked upstream L_meta_1942.
theorem supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem signal_support {pre : List Gate} (hg : ∀ g ∈ pre, g.inputs.length ≤ 2) (n : ℕ) (args : List ℕ) :
    ∃ s : Row (Fin n), s.card ≤ pre.length + 1 ∧ OnSupport (signal pre args) s := by
  cases args with
  | nil => exact ⟨∅,by simp,by intro x y _; rfl⟩
  | cons a args =>
    obtain ⟨S,hS,h⟩ := supports n pre hg {a}
    let s := Finset.univ.filter (fun i : Fin n => i.val ∈ S)
    have hsize : s.card ≤ S.card := Finset.card_le_card_of_injOn Fin.val (by intro i hi; exact (Finset.mem_filter.mp hi).2) (by
      intro _ _ _ _ he
      exact Fin.ext he)
    refine ⟨s,by simp only [Finset.card_singleton] at hS; omega,?_⟩
    intro x y eq
    apply h (input x) (input y) (by simp [input]) (by simp [input]) _ a (by simp)
    intro i hi
    by_cases inside : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa [input] using inside),
        List.getD_eq_getElem _ _ (by simpa [input] using inside)]
      simpa only [input,List.getElem_ofFn,decide_eq_decide] using
        eq ⟨i,inside⟩ (by simpa [s] using hi)
    · simp [input, Nat.le_of_not_lt inside]

theorem circuit_tests {pre post : List Gate} (hp : binaryMono pre) (ht : binaryMono post)
    (hg : ∀ g ∈ pre, g.inputs.length ≤ 2) (args : List ℕ) (o n : ℕ) (f : Row (Fin n) → Bool)
    (pass : ∀ x, (needed f x).card ≤ pre.length + 1 → out pre post args o x = f x) :
    ∀ x, out pre post args o x = f x := by
  obtain ⟨s,hs,hcut⟩ := signal_support hg n args
  exact tests_suffice f _ _ s hcut (circuit_on_slice hp ht args o n)
    (fun x h => pass x ((Finset.card_le_card h).trans hs))

end PEqualNP.Research.InverterCircuit

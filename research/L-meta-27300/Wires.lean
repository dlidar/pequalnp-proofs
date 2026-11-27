-- Wire evaluation and the unused-gate deletion proof adapted from upstream L_lib_376.
import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
def readGate (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_snoc_length readGate C.gates x

theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_of_initial (foldl_snoc_keeps readGate C.gates x) hi false

theorem wires_past (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  rw [wires_length]; exact hi

theorem wires_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (hback : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  obtain ⟨value, pre, len⟩ := foldl_snoc_split readGate C.gates x j hj false
  have hval : (C.wires x).getD (N + j) false = readGate ((C.gates.take j).foldl (fun R g => R ++ [readGate R g]) x) C.gates[j] := by
    rw [← hx]; exact value
  rw [hval]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < N + j := by
    have hb := hback j hj i
    rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
    exact hb hi
  have hpre_len : (List.foldl (fun R g => R ++ [readGate R g]) x (List.take j C.gates)).length = N + j := by
    rw [len, hx]
  exact (getD_of_initial pre (by omega) false).symm


end PEqualNP.Research.Permanent27300

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27535_aux
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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
def uses (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs
theorem insensitivity {m : ℕ} (C : Circuit) (ha : ReadsBack m C) (u : Fin m)
    (hu : u.val ∉ uses C) (x y : Fin m → Bool) (hxy : ∀ v ≠ u, x v = y v) :
    circuitFun m C x = circuitFun m C y := by
  have hw : ∀ a : ℕ, a ≠ u.val →
      (C.wires (List.ofFn x)).getD a false = (C.wires (List.ofFn y)).getD a false := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro hne
      by_cases h : a < m
      · rw [wires_low _ _ _ (by simpa using h), wires_low _ _ _ (by simpa using h)]
        simpa [List.getD_eq_getElem, h] using hxy ⟨a,h⟩ (fun h => hne (congrArg Fin.val h))
      by_cases hp : m + C.gates.length ≤ a
      · rw [wires_past _ _ _ (by simpa using hp),wires_past _ _ _ (by simpa using hp)]
      let j := a-m
      have hj : j < C.gates.length := by dsimp [j]; omega
      have eq : a = m+j := by dsimp [j]; omega
      rw [eq,wires_gate _ _ _ (List.length_ofFn ..) ha j hj,wires_gate _ _ _ (List.length_ofFn ..) ha j hj]
      congr 1
      apply List.map_congr_left
      intro b hb
      have back := ha j hj b
      rw [gateAt,List.getD_eq_getElem _ _ hj] at back
      apply ih b (eq ▸ back hb)
      intro e
      apply hu
      exact e ▸ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem .., hb⟩)
  exact hw _ (fun h => hu (by simp [uses,h]))


def first : Gate := ⟨.or,[0,1]⟩
def second : Gate := ⟨.and,[3,7]⟩
def px (s : Fin 512) (i : Fin 9) := s.val.testBit i.val
def perm3 (x : Fin 9 → Bool) := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
def extended (s : Fin 512) (i : Fin 11) : Bool :=
  if i.val = 9 then px s 0 || px s 1 else if i.val = 10 then px s 3 && px s 7 else s.val.testBit i.val
def pref (x : List Bool) := ([first,second] : List Gate).foldl (fun w g => w ++ [readGate w g]) x
theorem initial_rows : ∀ s : Fin 512, List.ofFn (extended s) = pref (List.ofFn (px s)) := by decide +kernel
def flip (i : Fin 9) : Fin 512 × Fin 512 := ([(162, 163), (97, 99), (80, 84), (258, 266), (68, 84), (66, 98), (20, 84), (33, 161), (10, 266)] : List (Fin 512 × Fin 512)).getD i.val (0,0)

theorem flips : ∀ i : Fin 9,
    (∀ j : Fin 11, j.val ≠ i.val → extended (flip i).1 j = extended (flip i).2 j) ∧
    perm3 (px (flip i).1) ≠ perm3 (px (flip i).2) := by decide +kernel

theorem early_eval (gs : List Gate) (o : ℕ) (s : Fin 512) :
    (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (px s)) =
    (Circuit.mk gs o).eval (List.ofFn (extended s)) := by
  rw [initial_rows]
  rfl

theorem raw_coverage {gs : List Gate} {o : ℕ}
    (hb : ReadsBack 11 ⟨gs,o⟩)
    (he : ∀ x, (Circuit.mk (first :: second :: gs) o).eval (List.ofFn x) = perm3 x) :
    ∀ i : Fin 9, i.val ∈ uses ⟨gs,o⟩ := by
  intro i
  by_contra hn
  let u : Fin 11 := ⟨i.val,by omega⟩
  have h := insensitivity ⟨gs,o⟩ hb u hn (extended (flip i).1) (extended (flip i).2) (by
    intro j hj
    exact (flips i).1 j (fun e => hj (Fin.ext e)))
  change (Circuit.mk gs o).eval _ = (Circuit.mk gs o).eval _ at h
  rw [← early_eval, ← early_eval,he,he] at h
  exact (flips i).2 h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Legal (m : ℕ) (g : Gate) := (g.op = .not ∧ ∃ a, a < m ∧ g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < m ∧ g.inputs = [a,b])

theorem legal_bounds {g : Gate} {m : ℕ} (h : Legal m g) :
    g.inputs.length ≤ 2 ∧ ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_,b,hb,e⟩ | ⟨_,a,b,hab,hb,e⟩
  · simp [e,hb]
  · simp [e,hb,hab.trans hb]

theorem tail_legal {gs : List Gate}
    (hg : ∀ j : Fin (first::second::gs).length, Legal (9+j.val) ((first::second::gs).get j)) :
    ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j) := by
  intro j
  have h := hg ⟨j.val+2, by simp <;> omega⟩
  simpa [show 9+(j.val+2) = 11+j.val by omega,List.get_eq_getElem] using h

theorem backward {gs : List Gate} (o : ℕ) (hg : ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j)) :
    ReadsBack 11 (Circuit.mk gs o) := by
  intro j hj a hm
  change a ∈ (gs.getD j _).inputs at hm
  rw [List.getD_eq_getElem _ _ hj] at hm
  exact (legal_bounds (hg ⟨j,hj⟩)).2 _ hm

theorem too_small (gs : List Gate) (o : ℕ) (sz : gs.length ≤ 9) (out : o+1 = 11+gs.length)
    (hg : ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j))
    (live : ∀ j : Fin (first::second::gs).length, j.val+1 < (first::second::gs).length →
      ∃ k : Fin (first::second::gs).length, j.val < k.val ∧
        9+j.val ∈ ((first::second::gs).get k).inputs)
    (he : ∀ x, (Circuit.mk (first::second::gs) o).eval (List.ofFn x) = perm3 x) :
    False := by
  have raws := raw_coverage (backward o hg) he
  have sub : List.range (11+gs.length) ⊆ uses ⟨gs,o⟩ := by
    intro w hw
    have bound := List.mem_range.mp hw
    by_cases h : w < 9
    · exact raws ⟨w,h⟩
    by_cases last : w = o
    · simp [uses,last]
    let j : Fin (first::second::gs).length := ⟨w-9,by simp <;> omega⟩
    have hj : j.val+1 < (first::second::gs).length := by dsimp [j]; simp; omega
    obtain ⟨k,_,hk⟩ := live j hj
    have eq : 9+j.val = w := by dsimp [j]; omega
    rw [eq] at hk
    have allm : w ∈ (first::second::gs).flatMap Gate.inputs := List.mem_flatMap.mpr ⟨_,List.get_mem (first::second::gs) k,hk⟩
    simp [first,second] at allm
    apply List.mem_cons_of_mem
    rcases allm with hh|hh|hh|hh|hh <;> first | omega | exact List.mem_flatMap.mpr hh | assumption
  have low := (List.subperm_of_subset List.nodup_range sub).length_le
  have lens : ∀ g ∈ gs, g.inputs.length ≤ 2 := by
    intro g hm
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hm
    exact (legal_bounds (hg ⟨j,hj⟩)).1
  have le : ∀ ls : List Gate, (∀ g ∈ ls, g.inputs.length ≤ 2) →
      (ls.flatMap Gate.inputs).length ≤ 2*ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons g gs ih =>
      intro H
      have := H g (by simp)
      have := ih fun g' hg' => H g' (by simp [hg'])
      simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega
  have hlen := le gs lens
  change (List.range (11+gs.length)).length ≤ (o::gs.flatMap Gate.inputs).length at low
  rw [List.length_cons,List.length_range] at low
  omega

end PEqualNP.Outside.L_meta_27535_aux

open PEqualNP.Outside.L_meta_27535_aux

theorem PEqualNP.Outside.L_meta_27535 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩) := by
  rintro ⟨⟨l,o⟩,_fan,sz,he,out,hg,_distinct,live,h0,h1⟩
  cases l with
  | nil => contradiction
  | cons g l =>
    cases l with
    | nil => contradiction
    | cons q gs =>
      change some g = some first at h0
      change some q = some second at h1
      obtain rfl := Option.some.inj h0
      obtain rfl := Option.some.inj h1
      apply too_small gs o _ _ (tail_legal hg) live he
      · change (first::second::gs).length ≤ 11 at sz
        simp at sz
        omega
      · change o+1 = 9+(first::second::gs).length at out
        simp at out
        omega

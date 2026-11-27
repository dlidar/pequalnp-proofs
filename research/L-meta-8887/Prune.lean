-- Wire evaluation and the unused-gate deletion proof adapted from upstream L_lib_376.
import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Research.Live8887
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

def shiftDel (p : ℕ) (w : ℕ) : ℕ :=
  if w < p then w else w - 1

def delGate (M : ℕ) (i₀ : ℕ) (C : Circuit) : Circuit :=
  let p := M + i₀
  let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDel p)⟩
  ⟨(C.gates.take i₀ ++ C.gates.drop (i₀ + 1)).map mapG, shiftDel p C.output⟩

theorem delGate_size {M i₀ : ℕ} {C : Circuit} (hi₀ : i₀ < C.gates.length) :
    (delGate M i₀ C).size = C.size - 1 := by
  unfold delGate Circuit.size
  simp [List.length_take, List.length_drop]
  omega

theorem delete_unused {M : ℕ} (C : Circuit) (i₀ : Fin C.gates.length)
    (hao : IsAO2 M C) (hout : M + i₀.val ≠ C.output)
    (hdead : ∀ j : Fin C.gates.length, i₀ < j → M + i₀.val ∉ (C.gates.get j).inputs) :
    let D := delGate M i₀.val C
    D.size + 1 = C.size ∧ IsAO2 M D ∧
    (∀ y : List Bool, y.length = M → D.eval y = C.eval y) := by
  have hback := hao.2.1
  let p := M + i₀.val
  let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDel p)⟩
  let gs' := C.gates.take i₀.val ++ C.gates.drop (i₀.val + 1)
  have hlen_gs' : gs'.length = C.gates.length - 1 := by
    simp [gs', List.length_take, List.length_drop]; omega
  have hlenD : (delGate M i₀.val C).gates.length = C.gates.length - 1 := by
    change (gs'.map mapG).length = _; simp [hlen_gs']
  have hno_read : ∀ (j : ℕ) (hj : j < C.gates.length), p ∉ C.gates[j].inputs := by
    intro j hj hmem
    by_cases hlt : i₀.val < j
    · exact hdead ⟨j, hj⟩ hlt (by simpa [List.get_eq_getElem] using hmem)
    · have hb := hback j hj p
      rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
      have := hb hmem
      omega
  have hgs'_get : ∀ (k : ℕ) (hk : k < gs'.length),
      gs'[k] = C.gates[if k < i₀.val then k else k + 1]'(by split_ifs <;> omega) := by
    intro k hk
    have htl : (C.gates.take i₀.val).length = i₀.val := by simp
    by_cases hki : k < i₀.val
    · simp only [gs', hki, ↓reduceIte]
      rw [List.getElem_append_left (by omega : k < (C.gates.take i₀.val).length), List.getElem_take]
    · simp only [gs', hki, ↓reduceIte]
      rw [List.getElem_append_right (by omega : (C.gates.take i₀.val).length ≤ k), List.getElem_drop]
      congr 1; omega
  have hgs'_mem : ∀ g ∈ gs', g ∈ C.gates := by
    intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact List.mem_of_mem_take h1
    · exact List.mem_of_mem_drop h2
  have hRB : ReadsBack M (delGate M i₀.val C) := by
    intro k hk w hw
    change k < (gs'.map mapG).length at hk
    have hk' : k < gs'.length := by simpa using hk
    have hgk : gateAt (delGate M i₀.val C) k = mapG gs'[k] := by
      unfold gateAt delGate
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map]
    rw [hgk] at hw
    simp only [mapG, List.mem_map] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [hgs'_get k hk'] at ha
    let idx := if k < i₀.val then k else k + 1
    have hidx : idx < C.gates.length := by dsimp [idx]; split_ifs <;> omega
    have hba := hback idx hidx a
    rw [gateAt, List.getD_eq_getElem _ _ hidx] at hba
    have halt : a < M + idx := hba ha
    have hne : a ≠ p := fun h => hno_read idx hidx (h ▸ ha)
    unfold shiftDel
    dsimp [idx] at halt
    split_ifs at halt ⊢ <;> omega
  refine ⟨by rw [delGate_size i₀.isLt]; have := i₀.isLt; unfold Circuit.size; omega, ⟨?_, hRB, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    exact hao.1 g0 (hgs'_mem g0 hg0)
  · intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    simpa using hao.2.2 g0 (hgs'_mem g0 hg0)
  · intro y hy
    have hw_eq : ∀ w : ℕ, w ≠ p →
        ((delGate M i₀.val C).wires y).getD (shiftDel p w) false = (C.wires y).getD w false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwp
        by_cases hlo : w < M
        · have hsd : shiftDel p w = w := by simp [shiftDel, show w < p by omega]
          rw [hsd, wires_low _ y w (by omega), wires_low _ y w (by omega)]
        by_cases hhi : M + C.gates.length ≤ w
        · have hsd : M + (delGate M i₀.val C).gates.length ≤ shiftDel p w := by
            rw [hlenD]; unfold shiftDel; split_ifs <;> omega
          rw [wires_past _ y _ (by omega), wires_past _ y _ (by omega)]
        let j := w - M
        have hj : j < C.gates.length := by omega
        have hwj : w = M + j := by omega
        have hji : j ≠ i₀.val := by omega
        let k := if j < i₀.val then j else j - 1
        have hk : k < gs'.length := by dsimp [k]; split_ifs <;> omega
        have hsd : shiftDel p w = M + k := by
          unfold shiftDel; dsimp [k]; split_ifs <;> omega
        rw [hsd, hwj]
        have hkD : k < (delGate M i₀.val C).gates.length := by rw [hlenD]; omega
        rw [wires_gate M (delGate M i₀.val C) y hy hRB k hkD]
        rw [wires_gate M C y hy hback j hj]
        have hgk : (delGate M i₀.val C).gates[k]'hkD = mapG C.gates[j] := by
          change (gs'.map mapG)[k]'(by rw [List.length_map]; exact hk) = mapG C.gates[j]
          rw [List.getElem_map, hgs'_get k hk]
          congr 2
          dsimp [k]; split_ifs <;> omega
        rw [hgk]
        simp only [mapG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < M + j := by
          have hb := hback j hj a
          rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
          exact hb ha
        have hap : a ≠ p := fun h => hno_read j hj (h ▸ ha)
        exact ih a (by omega) hap
    exact hw_eq C.output (Ne.symm hout)


def uses (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

theorem prune {m : ℕ} (C : Circuit) (ha : IsAO2 m C) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 m D ∧ circuitFun m D = circuitFun m C ∧
    ∀ j : Fin D.gates.length, m+j.val ∈ uses D := by
  classical
  by_cases h : ∀ j : Fin C.gates.length, m+j.val ∈ uses C
  · exact ⟨C, le_rfl, ha, rfl, h⟩
  push Not at h
  obtain ⟨i,hi⟩ := h
  have hno : m+i.val ≠ C.output := fun e => hi (by simp [uses,e])
  have hd : ∀ j : Fin C.gates.length, i < j → m+i.val ∉ (C.gates.get j).inputs := by
    intro j _ hm
    apply hi
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.get_mem _ _,hm⟩)
  obtain ⟨hlen,ha',he⟩ := delete_unused C i ha hno hd
  obtain ⟨D,hl,hD,hfun,hw⟩ := prune (delGate m i.val C) ha'
  refine ⟨D,by omega,hD,hfun.trans ?_,hw⟩
  funext x
  exact he _ (List.length_ofFn ..)
termination_by C.size
decreasing_by omega
#print axioms prune
end PEqualNP.Research.Live8887

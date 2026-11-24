import PEqualNP.Defs

namespace PEqualNP.Research.FlagTangent
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

-- The generic scan lemmas are from the project’s L-meta-2970.
def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢


theorem track : ∀ (C : Circuit) (a b : Fin 26) (d : ℕ → Bool),
      let w := fun j => wireVal 26 C j (pairInput a a)
      a ≠ b → IsAO2 26 C →
      (∀ i < 26, d i = decide (i = b.val)) →
      (∀ k (g : Gate) u v, C.gates[k]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (26+k) = ((w u && d v) || (d u && w v))) ∧
        (g.op = .or → d (26+k) = (d u || d v))) →
      PEqualNP.ReadK.lineSingle C 26 (fun i => i == b.val) a.val b.val = true →
      d C.output = true := by
  intro C a b d w hab hAO base rec single
  let xs := (List.range 26).map fun i => i == a.val || i == b.val
  let init := xs.zipIdx.map fun (t,i) => if i == b.val then (false,t) else (t,false)
  let ws := scan linStep C.gates init
  let raw := List.ofFn (pairInput a a)
  have il : init.length = 26 := by simp [init,xs]
  have rl : raw.length = 26 := by simp [raw]
  have al : ws.length = 26 + C.gates.length := by simp [ws,scan_length,il]
  have finNe : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have inp (i : ℕ) (hi : i < 26) : init.getD i (false,false) =
      (decide (i = a.val), decide (i = b.val)) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [init,List.getElem_map,List.getElem_zipIdx,xs,List.getElem_range,Nat.zero_add]
    by_cases hb : i = b.val
    · simp [hb,Ne.symm finNe]
    · have eb : (i == b.val) = false := by simpa using hb
      by_cases ha : i = a.val
      · simp [ha,finNe]
      · have ea : (i == a.val) = false := by simpa using ha
        simp [eb,ea,ha,hb]
  have wires (i : ℕ) (hi : i < ws.length) :
      ws.getD i (false,false) = (w i,d i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases small : i < 26
      · rw [show ws.getD i (false,false) = init.getD i (false,false) from
               scan_prefix _ _ _ _ _ (by omega), inp i small, base i small]
        congr 1
        change _ = (scan boolStep C.gates raw).getD i false
        rw [scan_prefix _ _ _ _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
        simp only [raw,List.getElem_ofFn,pairInput,or_self,Fin.ext_iff]
      · let j := i-26
        have hj : j < C.gates.length := by dsimp [j]; omega
        have ij : i = 26+j := by dsimp [j]; omega
        let g := C.gates[j]
        have gg : C.gates[j]? = some g := by simp [g,hj]
        have gm : g ∈ C.gates := List.getElem_mem _
        have hargs := list_eq_two (hAO.2.2 g gm)
        let u := g.inputs.getD 0 0
        let v := g.inputs.getD 1 0
        change g.inputs = [u,v] at hargs
        have rb : ∀ t ∈ g.inputs, t < i := by
          intro t ht
          rw [ij]
          apply hAO.2.1 j hj
          change t ∈ (C.gates.getD j ⟨.or,[]⟩).inputs
          rw [List.getD_eq_getElem _ _ hj]; exact ht
        have rbu := rb u (by simp [hargs])
        have rbv := rb v (by simp [hargs])
        have step {α : Type} (s : List α → Gate → α) (z : List α) (dz : α)
            (len : z.length = 26)
            (locality : ∀ q t, q.getD u dz = t.getD u dz →
              q.getD v dz = t.getD v dz → s q g = s t g) :
            (scan s C.gates z).getD i dz = s (scan s C.gates z) g := by
          rw [ij,← len]
          apply scan_gate _ _ _ _ _ hj
          intro q t eqs
          exact locality q t (eqs u (by omega)) (eqs v (by omega))
        have lhs := step linStep init (false,false) il (by
          intro q t h1 h2; simp only [linStep,hargs,List.map_cons,List.map_nil,h1,h2])
        have rhs := step boolStep raw false rl (by
          intro q t h1 h2; simp only [boolStep,hargs,List.map_cons,List.map_nil,h1,h2])
        change ws.getD i (false,false) = linStep ws g at lhs
        have vu := ih u rbu (by omega)
        have vv := ih v rbv (by omega)
        have rule := rec j g u v gg hargs
        rw [lhs]
        change w i = _ at rhs
        rw [rhs]
        rcases hAO.1 g gm with op | op
        · rw [ij,rule.1 op]
          simp only [linStep, boolStep, op, hargs, List.map_cons, List.map_nil, List.foldl_cons,
            List.foldl_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.true_and, Bool.false_and,
            Bool.or_false, Bool.and_true, vu, vv]
          rfl
        · rw [ij,rule.2 op]
          simp only [linStep, boolStep, op, hargs, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, GateOp.eval, Bool.or_false, vu, vv]
          rfl
  change (ws.getD C.output (false,false)).2 = true at single
  by_cases inside : C.output < ws.length
  · simpa only [wires C.output inside] using single
  · rw [List.getD_eq_default _ _ (by omega)] at single
    contradiction
end PEqualNP.Research.FlagTangent

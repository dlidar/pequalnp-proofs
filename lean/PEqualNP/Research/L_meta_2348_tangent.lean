import PEqualNP.Defs

namespace PEqualNP.Research.FanoTangent
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

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢


theorem track {n : ℕ} : ∀ (C : Circuit) (a b : Fin n) (d : ℕ → Bool),
      let w := fun j => wireVal n C j (pairInput a a)
      a ≠ b → IsAO2 n C →
      (∀ i < n, d i = decide (i = b.val)) →
      (∀ k (g : Gate) u v, C.gates[k]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (n+k) = ((w u && d v) || (d u && w v))) ∧
        (g.op = .or → d (n+k) = (d u || d v))) →
      PEqualNP.ReadK.lineSingle C n (fun i => i == b.val) a.val b.val = true →
      d C.output = true := by
  intro C a b d w hab hAO base rec single
  let xs := (List.range n).map fun i => i == a.val || i == b.val
  let init := xs.zipIdx.map fun (t,i) => if i == b.val then (false,t) else (t,false)
  let ws := scan linStep C.gates init
  let raw := List.ofFn (pairInput a a)
  have il : init.length = n := by simp [init,xs]
  have rl : raw.length = n := by simp [raw]
  have al : ws.length = n + C.gates.length := by simp [ws,scan_length,il]
  have finNe : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have inp (i : ℕ) (hi : i < n) : init.getD i (false,false) =
      (decide (i = a.val), decide (i = b.val)) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [init,List.getElem_map,List.getElem_zipIdx,xs,List.getElem_range,Nat.zero_add]
    by_cases hb : i = b.val
    · have ha : i ≠ a.val := by omega
      simp [hb,Ne.symm finNe]
    · have eb : (i == b.val) = false := by simpa using hb
      by_cases ha : i = a.val
      · simp [eb,ha,finNe]
      · have ea : (i == a.val) = false := by simpa using ha
        simp [eb,ea,ha,hb]
  have wires (i : ℕ) (hi : i < ws.length) :
      ws.getD i (false,false) = (w i,d i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases small : i < n
      · rw [show ws.getD i (false,false) = init.getD i (false,false) from
               scan_prefix _ _ _ _ _ (by omega), inp i small, base i small]
        congr 1
        change _ = (scan boolStep C.gates raw).getD i false
        rw [scan_prefix _ _ _ _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
        simp only [raw,List.getElem_ofFn,pairInput,or_self,Fin.ext_iff]
      · let j := i-n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have ij : i = n+j := by dsimp [j]; omega
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
            (len : z.length = n)
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
          simp only [linStep,boolStep,op,hargs,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil, List.any_cons,List.any_nil,GateOp.eval,List.all_cons,List.all_nil, Bool.true_and,Bool.false_and,Bool.or_false,Bool.false_or,Bool.and_true,vu,vv] <;> rfl
        · rw [ij,rule.2 op]
          simp only [linStep,boolStep,op,hargs,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil, List.any_cons,List.any_nil,GateOp.eval,List.all_cons,List.all_nil, Bool.true_and,Bool.false_and,Bool.or_false,Bool.false_or,Bool.and_true,vu,vv] <;> rfl
  change (ws.getD C.output (false,false)).2 = true at single
  by_cases inside : C.output < ws.length
  · simpa only [wires C.output inside] using single
  · rw [List.getD_eq_default _ _ (by omega)] at single
    contradiction

open PEqualNP.MetaComplexity.NestedCover

theorem tangent_false {n : ℕ} (C : Circuit) (a b : Fin n) (d : ℕ → Bool)
    (hab : a ≠ b) (hAO : IsAO2 n C)
    (base : ∀ i < n, d i = decide (i = b.val))
    (rec : ∀ j < C.size,
      let w := C.wires (List.ofFn fun i : Fin n => decide (i = a))
      let u := opnd C j 0
      let v := opnd C j 1
      ((gateAt C j).op = .and → d (n+j) = ((w.getD u false && d v) || (d u && w.getD v false))) ∧
      ((gateAt C j).op = .or → d (n+j) = (d u || d v)))
    (hout : d C.output = false) :
    lineSingle C n (fun i => i == b.val) a.val b.val = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := track C a b d hab hAO base (by
    intro k g u v hg hi
    have hk : k < C.size := by
      change k < C.gates.length
      exact List.getElem?_eq_some_iff.mp hg |>.choose
    have eqg : gateAt C k = g := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD,hg]
    dsimp only
    have hp : pairInput a a = (fun i => decide (i = a)) := by funext i; simp [pairInput]
    simpa [wireVal, hp, opnd, eqg, hi] using rec k hk) h
  rw [hout] at hh
  contradiction

theorem linear_child : ∀ C : Circuit, IsAO2 14 C →
    ∀ (s : Bool) (v : ℕ → Bool),
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) → v C.output = false → PEqualNP.ReadK.lineSingle C 14 (fun i => i == (if s then 7 else 0)) 0 7 = false := by
  intro C hAO s d W base rec hout
  cases s with
  | true => exact tangent_false C (0 : Fin 14) 7 d (by decide) hAO base rec hout
  | false =>
    have h := tangent_false C (7 : Fin 14) 0 d (by decide) hAO base rec hout
    change lineSingle C 14 (fun i => i == 0) 7 0 = false at h
    change lineSingle C 14 (fun i => i == 0) 0 7 = false
    unfold lineSingle at h ⊢
    simpa only [Bool.or_comm] using h

#print axioms track
#print axioms tangent_false
#print axioms linear_child
end PEqualNP.Research.FanoTangent

import PEqualNP.Research.L_meta_2348_tangent

namespace PEqualNP.Research.L_meta_2348_polynomial

/-- Terms of the monotone Boolean formula after variables outside a flag are set false.
An entry counts point leaves and line leaves in one parse tree, with multiplicity. -/
abbrev Terms := List (ℕ × ℕ)

def product (xs ys : Terms) : Terms :=
  xs.flatMap fun a => ys.map fun b => (a.1 + b.1, a.2 + b.2)

def hasDegree (line : Bool) (d : ℕ) (xs : Terms) : Prop :=
  ∃ a ∈ xs, (if line then a.2 else a.1) = d

theorem sum_hasDegree (s : Bool) (d : ℕ) (xs ys : Terms) :
    hasDegree s d (xs ++ ys) ↔ hasDegree s d xs ∨ hasDegree s d ys := by
  simp only [hasDegree, List.mem_append]
  aesop

theorem product_hasDegree (s : Bool) (d : ℕ) (xs ys : Terms) :
    hasDegree s d (product xs ys) ↔ ∃ i j, i + j = d ∧ hasDegree s i xs ∧ hasDegree s j ys := by
  cases s <;> simp only [hasDegree, product, List.mem_flatMap, List.mem_map, Bool.false_eq_true,
    ↓reduceIte] <;> constructor
  all_goals first
    | rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨_, _, rfl, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    | rintro ⟨_, _, rfl, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩

theorem constant_product (s : Bool) (xs ys : Terms) :
    hasDegree s 0 (product xs ys) ↔ hasDegree s 0 xs ∧ hasDegree s 0 ys := by
  rw [product_hasDegree]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    exact ⟨hi,hj⟩
  · rintro ⟨h,k⟩; exact ⟨0,0,rfl,h,k⟩

theorem linear_product (s : Bool) (xs ys : Terms) :
    hasDegree s 1 (product xs ys) ↔
      (hasDegree s 0 xs ∧ hasDegree s 1 ys) ∨ (hasDegree s 1 xs ∧ hasDegree s 0 ys) := by
  rw [product_hasDegree]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨hi,hj⟩
    · exact Or.inr ⟨hi,hj⟩
  · rintro (⟨h,k⟩ | ⟨h,k⟩)
    · exact ⟨0,1,rfl,h,k⟩
    · exact ⟨1,0,rfl,h,k⟩

/-- A structurally unfolded AND/OR wire can include repeated subtrees. -/
inductive Tree
  | zero | point | line
  | meet (a b : Tree) | join (a b : Tree)

def Tree.terms : Tree → Terms
  | .zero => [] | .point => [(1,0)] | .line => [(0,1)]
  | .meet a b => product a.terms b.terms | .join a b => a.terms ++ b.terms

/-- The first component is the wire value at the opposite endpoint of the flag.
The second component is the linear response in the direction of this endpoint. -/
def Tree.jet (s : Bool) : Tree → Bool × Bool
  | .zero => (false,false) | .point => (s,!s) | .line => (!s,s)
  | .join a b => ((a.jet s).1 || (b.jet s).1, (a.jet s).2 || (b.jet s).2)
  | .meet a b => ((a.jet s).1 && (b.jet s).1,
      ((a.jet s).1 && (b.jet s).2) || ((a.jet s).2 && (b.jet s).1))

theorem Tree.coefficients (s : Bool) (t : Tree) :
    ((t.jet s).1 = true ↔ hasDegree s 0 t.terms) ∧
    ((t.jet s).2 = true ↔ hasDegree s 1 t.terms) := by
  induction t with
  | zero | point | line => cases s <;> simp [jet, terms, hasDegree]
  | join a b ha hb => simp [jet, terms, sum_hasDegree, ha.1, ha.2, hb.1, hb.2]
  | meet a b ha hb => simp [jet, terms, constant_product, linear_product, ha.1, ha.2, hb.1, hb.2]

theorem four_leaves_iff (t : Tree) :
    (t.jet false = (false,false) ∧ t.jet true = (false,false)) ↔
    ∀ e ∈ t.terms, 2 ≤ e.1 ∧ 2 ≤ e.2 := by
  have a := t.coefficients false
  have b := t.coefficients true
  simp only [Prod.ext_iff, Bool.eq_false_iff, hasDegree, Bool.false_eq_true, ↓reduceIte] at *
  constructor
  · intro h e he
    constructor
    · by_contra! h'
      rcases (show e.1 = 0 ∨ e.1 = 1 by omega) with hz | hz
      · exact h.1.1 (a.1.mpr ⟨e,he,hz⟩)
      · exact h.1.2 (a.2.mpr ⟨e,he,hz⟩)
    · by_contra! h'
      rcases (show e.2 = 0 ∨ e.2 = 1 by omega) with hz | hz
      · exact h.2.1 (b.1.mpr ⟨e,he,hz⟩)
      · exact h.2.2 (b.2.mpr ⟨e,he,hz⟩)
  · intro h
    constructor <;> constructor
    all_goals intro h'
    · obtain ⟨e,he,hd⟩ := a.1.mp h'; have := (h e he).1; omega
    · obtain ⟨e,he,hd⟩ := a.2.mp h'; have := (h e he).1; omega
    · obtain ⟨e,he,hd⟩ := b.1.mp h'; have := (h e he).2; omega
    · obtain ⟨e,he,hd⟩ := b.2.mp h'; have := (h e he).2; omega

#print axioms four_leaves_iff
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Research.FanoTangent

def treeStep (w : List Tree) (g : Gate) : Tree :=
  let a := w.getD (g.inputs.getD 0 0) .zero
  let b := w.getD (g.inputs.getD 1 0) .zero
  match g.op with
  | .and => .meet a b
  | .or => .join a b
  | _ => .zero

def leaf (a b i : ℕ) : Tree := if i = a then .point else if i = b then .line else .zero

def treeWires (C : Circuit) (n a b : ℕ) : List Tree :=
  scan treeStep C.gates ((List.range n).map (leaf a b))

theorem map_wire (s : Bool) (w : List Tree) (i : ℕ) :
    (w.map (Tree.jet s)).getD i (false,false) = (w.getD i .zero).jet s := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

theorem eval_gate (s : Bool) (w : List Tree) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length = 2) :
    (treeStep w g).jet s = linStep (w.map (Tree.jet s)) g := by
  have args := list_eq_two arity
  generalize ha : g.inputs.getD 0 0 = a at args ⊢
  generalize hb : g.inputs.getD 1 0 = b at args ⊢
  rcases op with h | h <;>
    simp [treeStep, linStep, h, args, Tree.jet] <;>
    cases w[a]? <;> cases w[b]? <;> simp [Tree.jet]

theorem scan_map (s : Bool) (gs : List Gate) (w : List Tree)
    (good : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (scan treeStep gs w).map (Tree.jet s) = scan linStep gs (w.map (Tree.jet s)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [scan_cons]
    rw [ih _ (fun g hg => good g (List.mem_cons_of_mem _ hg))]
    rw [List.map_append, List.map_singleton, eval_gate s w g (good g (by simp)).1 (good g (by simp)).2]

theorem initials (s : Bool) (a b n : ℕ) (hab : a ≠ b) :
    (((List.range n).map (leaf a b)).map (Tree.jet s)) =
    (((List.range n).map (fun i => i == a || i == b)).zipIdx).map
      (fun (t,i) => if (if s then i == b else i == a) then (false,t) else (t,false)) := by
  apply List.ext_getElem
  · simp
  · intro i h h'
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, Nat.zero_add]
    by_cases ha : i = a <;> by_cases hb : i = b <;> cases s <;>
      simp_all [leaf, Tree.jet, beq_iff_eq]

theorem jet_wires (C : Circuit) {n : ℕ} (hAO : IsAO2 n C) (a b : ℕ) (hab : a ≠ b) (s : Bool) :
    (treeWires C n a b).map (Tree.jet s) =
      linearParts C (fun i => if s then i == b else i == a)
        ((List.range n).map fun i => i == a || i == b) := by
  rw [linearParts_eq_scan, treeWires, scan_map _ _ _ (fun g hg => ⟨hAO.1 g hg,hAO.2.2 g hg⟩)]
  rw [initials s a b n hab]

/-- Both oriented linear readings vanish precisely when every surviving parse term
avoids degree one in both coordinates. If singleton evaluations vanish as well,
each parse of the flag must contain two copies of each endpoint. -/
theorem single_iff_term (C : Circuit) {n : ℕ} (hAO : IsAO2 n C) (a b : ℕ) (hab : a ≠ b) (s : Bool) :
    lineSingle C n (fun i => if s then i == b else i == a) a b = true ↔
      hasDegree s 1 (((treeWires C n a b).getD C.output .zero).terms) := by
  unfold lineSingle
  rw [← jet_wires C hAO a b hab s, map_wire]
  exact ((Tree.coefficients s _).2)

#print axioms single_iff_term


theorem constant_gate (s : Bool) (w : List Tree) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length = 2) :
    ((treeStep w g).jet s).1 = boolStep (w.map (fun t => (t.jet s).1)) g := by
  have args := list_eq_two arity
  generalize ha : g.inputs.getD 0 0 = a at args ⊢
  generalize hb : g.inputs.getD 1 0 = b at args ⊢
  rcases op with h | h <;>
    simp [treeStep, boolStep, h, args, Tree.jet, GateOp.eval] <;>
    cases w[a]? <;> cases w[b]? <;> simp [Tree.jet]

theorem constant_scan (s : Bool) (gs : List Gate) (w : List Tree)
    (good : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (scan treeStep gs w).map (fun t => (t.jet s).1) =
      scan boolStep gs (w.map (fun t => (t.jet s).1)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [scan_cons]
    rw [ih _ (fun g hg => good g (List.mem_cons_of_mem _ hg))]
    rw [List.map_append, List.map_singleton, constant_gate s w g (good g (by simp)).1 (good g (by simp)).2]

theorem constant_output (C : Circuit) {n : ℕ} (hAO : IsAO2 n C) (a b : Fin n)
    (hab : a ≠ b) (s : Bool) :
    ((((treeWires C n a.val b.val).getD C.output .zero).jet s).1) =
      C.eval (List.ofFn fun i : Fin n => decide (i = if s then a else b)) := by
  have ini : (((List.range n).map (leaf a.val b.val)).map (fun t => (t.jet s).1)) =
      List.ofFn (fun i : Fin n => decide (i = if s then a else b)) := by
    apply List.ext_getElem
    · simp
    · intro i h h'
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      have ne : a.val ≠ b.val := fun h => hab (Fin.ext h)
      cases s <;> by_cases ha : i = a.val <;> by_cases hb : i = b.val <;>
        simp_all [leaf,Tree.jet,Fin.ext_iff]
  have e := constant_scan s C.gates ((List.range n).map (leaf a.val b.val)) (fun g hg => ⟨hAO.1 g hg,hAO.2.2 g hg⟩)
  rw [ini] at e
  change _ = (scan boolStep C.gates _).getD C.output false
  rw [← e]
  unfold treeWires
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (scan treeStep C.gates ((List.range n).map (leaf a.val b.val)))[C.output]? <;> rfl

/-- For a circuit false at the two singleton inputs, absence of both oriented
linear responses is equivalent to a constraint on *every* parse tree at the pair. -/
theorem double_read_iff (C : Circuit) {n : ℕ} (hAO : IsAO2 n C) (a b : Fin n)
    (hab : a ≠ b)
    (hn : ∀ k ∈ [a,b], C.eval (List.ofFn fun i : Fin n => decide (i = k)) = false) :
    (∀ s : Bool, lineSingle C n (fun i => if s then i == b.val else i == a.val) a.val b.val = false) ↔
      ∀ e ∈ ((treeWires C n a.val b.val).getD C.output .zero).terms, 2 ≤ e.1 ∧ 2 ≤ e.2 := by
  rw [← four_leaves_iff]
  let t := (treeWires C n a.val b.val).getD C.output Tree.zero
  have f (s : Bool) : (t.jet s).1 = false := by
    rw [show (t.jet s).1 = _ from constant_output C hAO a b hab s]
    apply hn
    cases s <;> simp
  have same (s : Bool) : lineSingle C n (fun i => if s then i == b.val else i == a.val)
      a.val b.val = (t.jet s).2 := by
    unfold lineSingle
    rw [← jet_wires C hAO _ _ (fun h => hab (Fin.ext h)) s, map_wire]
  constructor
  · intro h
    exact ⟨Prod.ext (f false) ((same false).symm.trans (h false)),
      Prod.ext (f true) ((same true).symm.trans (h true))⟩
  · intro h s
    rw [same]
    cases s
    · exact congrArg Prod.snd h.1
    · exact congrArg Prod.snd h.2

#print axioms double_read_iff
end PEqualNP.Research.L_meta_2348_polynomial

import PEqualNP.Research.L_meta_2584_budget

namespace PEqualNP.Research.ReadTwoTradeoff
open PEqualNP.ReadK PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Research.ReadTwoBudget

/-- Start with the union and intersection of the two raw wires. Repeatedly
intersect the previous output with their union, always reading distinct wires. -/
def gates : ℕ → List Gate
  | 0 => [⟨.or,[0,1]⟩,⟨.and,[0,1]⟩]
  | t+1 => gates t ++ [⟨.and,[2,3+t]⟩]
def chain (t : ℕ) : Circuit := ⟨gates t,3+t⟩

theorem length_gates (t : ℕ) : (gates t).length = 2+t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [gates,ih]; omega

def cap (k a b : ℕ) : List ℕ := [min a (k+1), min b (k+1)]
lemma cap_sum (k a b c d : ℕ) : capAdd k (cap k a b) (cap k c d) = cap k (a+c) (b+d) := by
  simp only [cap,capAdd,List.zipWith_cons_cons,List.zipWith_nil_left,List.cons.injEq]
  constructor
  · omega
  · constructor
    · omega
    · trivial

lemma product_mem (k : ℕ) (A B : Bag) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, capAdd k u w = v := by
  simp [andStep,union_mem,List.mem_flatMap,List.mem_map]

def table (t k : ℕ) := readVectors (chain t) 2 [0,1] k
lemma table_length (t k : ℕ) : (table t k).length = 4+t := by
  unfold table readVectors
  have h {α : Type} (w : List α) (gs : List Gate) (f : List α → Gate → α) :
      (gs.foldl (fun l g => l ++ [f l g]) w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]; omega
  rw [h]
  simp [chain,length_gates]; omega

def mix : Bag := [[1,0],[0,1]]
lemma base_table (k : ℕ) : table 0 k = [[[1,0]],[[0,1]],mix,[[1,1]]] := by
  cases k <;> rfl

lemma table_succ (t k : ℕ) :
    table (t+1) k = table t k ++ [andStep k
      (andStep k [[0,0]] ((table t k).getD 2 [])) ((table t k).getD (3+t) [])] := by
  simp only [table,readVectors,chain,gates,List.foldl_append]; rfl

lemma mix_wire (t k : ℕ) : (table t k).getD 2 [] = mix := by
  induction t with
  | zero => rw [base_table]; rfl
  | succ t ih =>
    rw [table_succ,List.getD_append _ _ _ _ (by rw [table_length]; omega),ih]

def output (t k : ℕ) := (table t k).getD (3+t) []
lemma output_succ (t k : ℕ) : output (t+1) k = andStep k (andStep k [[0,0]] mix) (output t k) := by
  unfold output; rw [table_succ,mix_wire]
  rw [show 3+(t+1) = (table t k).length by rw [table_length]; omega]
  simp [List.getD_eq_getElem?_getD]

lemma first_factor (k : ℕ) :
    andStep k [[0,0]] mix = [cap k 1 0,cap k 0 1] := by cases k <;> rfl

/-- Exact joint counts on the unique edge, even when the read counter saturates. -/
theorem output_counts (t k : ℕ) (v : List ℕ) :
    v ∈ output t k ↔ ∃ a b : ℕ, a+b=t ∧ cap k (1+a) (1+b) = v := by
  induction t generalizing v with
  | zero =>
    rw [output,base_table]
    change v ∈ [[1,1]] ↔ _
    constructor
    · intro h; have e := List.mem_singleton.mp h
      exact ⟨0,0,rfl,by cases k <;> simp_all [cap]⟩
    · rintro ⟨a,b,h,rfl⟩
      obtain rfl : a = 0 := by omega
      obtain rfl : b = 0 := by omega
      cases k <;> simp [cap]
  | succ t ih =>
    rw [output_succ,first_factor,product_mem]
    constructor
    · rintro ⟨u,hu,w,hw,rfl⟩
      obtain ⟨a,b,hab,rfl⟩ := (ih w).mp hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl | rfl <;> rw [cap_sum]
      · exact ⟨a+1,b,by omega,by congr 1 <;> omega⟩
      · exact ⟨a,b+1,by omega,by congr 1 <;> omega⟩
    · rintro ⟨a,b,hab,rfl⟩
      cases a with
      | succ a =>
        exact ⟨_,List.mem_cons_self,_,(ih _).mpr ⟨a,b,by omega,rfl⟩,by rw [cap_sum]; congr 1 <;> omega⟩
      | zero =>
        have e : b = t+1 := by omega
        subst b
        exact ⟨cap k 0 1,by simp,_,(ih _).mpr ⟨0,t,by omega,rfl⟩,by rw [cap_sum]; congr 1 <;> omega⟩

theorem joint_budget (t k : ℕ) :
    readsAtMost (chain t) 2 [0,1] k = true ↔ t+2 ≤ 2*k := by
  change (output t k).any _ = true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v,hv,good⟩
    obtain ⟨a,b,h,rfl⟩ := (output_counts t k v).mp hv
    simp [cap] at good
    omega
  · intro h
    let a := t/2
    let b := t-a
    have ha : a+b=t := by dsimp [a,b]; omega
    refine ⟨_,(output_counts _ _ _).mpr ⟨a,b,ha,rfl⟩,?_⟩
    simp [cap,a,b]; omega

#print axioms output_counts
#print axioms joint_budget
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity

theorem gate_description (t j : ℕ) (hj : j < (gates t).length) :
    let g := (gates t).getD j ⟨.or,[]⟩
    (g.op = .and ∨ g.op = .or) ∧
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 2+j ∧ b < 2+j := by
  induction t with
  | zero =>
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨Or.inr rfl,0,1,rfl,by decide,by decide,by decide⟩
    · exact ⟨Or.inl rfl,0,1,rfl,by decide,by decide,by decide⟩
  | succ t ih =>
    by_cases old : j < (gates t).length
    · simpa only [gates,List.getD_append _ _ _ _ old] using ih old
    · have eqj : j = (gates t).length := by
        rw [length_gates] at hj old ⊢; omega
      subst j
      simp [gates,List.getD_eq_getElem?_getD,List.getElem?_append_right,length_gates]
      omega

theorem strict (t : ℕ) : IsAO2 2 (chain t) := by
  have m (g : Gate) (hg : g ∈ (gates t)) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hg
    have H := gate_description t j hj
    rw [List.getD_eq_getElem _ _ hj,e] at H
    obtain ⟨hop,a,b,eq,_⟩ := H
    exact ⟨hop,by simp [eq]⟩
  refine ⟨fun g hg => (m g hg).1, ?_,fun g hg => (m g hg).2⟩
  intro j hj i hi
  obtain ⟨_,a,b,eq,_,ha,hb⟩ := gate_description t j hj
  change i ∈ ((gates t).getD j ⟨.or,[]⟩).inputs at hi
  rw [eq] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl <;> assumption

theorem operands_distinct (t : ℕ) : ∀ j < (chain t).size, opnd (chain t) j 0 ≠ opnd (chain t) j 1 := by
  intro j hj
  obtain ⟨_,a,b,eq,ne,_⟩ := gate_description t j hj
  have e : (gateAt (chain t) j).inputs = [a,b] := eq
  unfold opnd
  rw [e]
  exact ne

theorem fold_len {α : Type} (f : List α → Gate → α) (w : List α) (gs : List Gate) :
    (gs.foldl (fun l g => l ++ [f l g]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]; omega

theorem truth_trace (t : ℕ) (p l : Bool) :
    let w := (chain t).wires [p,l]
    w.getD 2 false = (p || l) ∧ w.getD (3+t) false = (p && l) := by
  induction t with
  | zero => cases p <;> cases l <;> decide
  | succ t ih =>
    let w := (chain t).wires [p,l]
    have len : w.length = 4+t := by
      unfold w Circuit.wires
      rw [fold_len]; simp [chain,length_gates]; omega
    have e : (chain (t+1)).wires [p,l] =
        w ++ [w.getD 2 false && w.getD (3+t) false] := by
      simp only [chain,Circuit.wires,gates,List.foldl_append,List.foldl_cons,List.foldl_nil,
        List.map_cons,List.map_nil, GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
      rfl
    change w.getD 2 false = _ ∧ w.getD (3+t) false = _ at ih
    dsimp only
    rw [e,List.getD_append _ _ _ 2 (by omega),show 3+(t+1) = w.length by omega]
    simp [List.getD_eq_getElem?_getD] at ih ⊢
    rw [ih.1,ih.2]
    cases p <;> cases l <;> decide

theorem edge_fun (t : ℕ) (x : Fin 2 → Bool) :
    circuitFun 2 (chain t) x = (x 0 && x 1) := by
  exact (truth_trace t (x 0) (x 1)).2

theorem scalar_trace (t : ℕ) (i : Fin 2) :
    let w := scalarMults (chain t) 2 [0,1] i.val
    w.getD 2 none = some 0 ∧ w.getD (3+t) none = some 1 := by
  induction t with
  | zero => fin_cases i <;> decide
  | succ t ih =>
    let w := scalarMults (chain t) 2 [0,1] i.val
    have len : w.length = 4+t := by
      unfold w scalarMults
      rw [fold_len]; simp [chain,length_gates]; omega
    have e : scalarMults (chain (t+1)) 2 [0,1] i.val = w ++ [some 1] := by
      change w.getD 2 none = _ ∧ w.getD (3+t) none = _ at ih
      unfold scalarMults chain
      rw [gates,List.foldl_append]
      change w ++ [List.foldl _ (some 0) [w.getD 2 none,w.getD (3+t) none]] = _
      rw [ih.1,ih.2]; rfl
    dsimp only
    rw [e,List.getD_append _ _ _ 2 (by omega),show 3+(t+1) = w.length by omega]
    exact ⟨ih.1,by simp [List.getD_eq_getElem?_getD]⟩

theorem scalar_one (t : ℕ) : eachReadsAtMost (chain t) 2 [0,1] 1 = true := by
  have a := (scalar_trace t (0 : Fin 2)).2
  have b := (scalar_trace t (1 : Fin 2)).2
  change (scalarMults (chain t) 2 [0,1] 0).getD (chain t).output none = some 1 at a
  change (scalarMults (chain t) 2 [0,1] 1).getD (chain t).output none = some 1 at b
  simp only [List.getD_eq_getElem?_getD] at a b
  simp [eachReadsAtMost,a,b]

/-- The growing gap is a property of the given circuit. The entire family
has a one-gate replacement which reads both inputs once. -/
def direct : Circuit := ⟨[⟨.and,[0,1]⟩],2⟩

theorem direct_read_once : IsAO2 2 direct ∧ IsReadK 2 direct 1 := by decide +kernel

theorem normalize_chain (t : ℕ) :
    IsAO2 2 direct ∧ IsReadK 2 direct 1 ∧ direct.size ≤ (chain t).size ∧
    circuitFun 2 direct = circuitFun 2 (chain t) := by
  refine ⟨direct_read_once.1,direct_read_once.2,?_,?_⟩
  · change 1 ≤ (gates t).length
    rw [length_gates]; omega
  · funext x
    rw [edge_fun]
    have eval (p l : Bool) : direct.eval [p,l] = (p && l) := by cases p <;> cases l <;> decide
    exact eval (x 0) (x 1)

#print axioms strict
#print axioms edge_fun
#print axioms scalar_one
end PEqualNP.Research.ReadTwoTradeoff

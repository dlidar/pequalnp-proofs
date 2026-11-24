import PEqualNP.Defs.MetaComplexityLgpMono

-- Partial result for L-meta-1895. The final equivalence leaves open the
-- existence of a circuit computing incidence within the stated size bound.
namespace MarkedWitness

-- A large input is represented by its two-coordinate restrictions.
-- Each true wire has one coordinate sufficient to keep it true on every
-- tested pair containing that coordinate, until some conjunction fires.
def Covers (w : List Bool) (t : Nat → Nat → List Bool) : Prop :=
  ∀ i, w.getD i false = true → ∃ p, ∀ q,
    (t p q).getD i false = true ∧ (t q p).getD i false = true

def step (gate : Bool × List Nat) (w : List Bool) : Bool :=
  if gate.1 then gate.2.all (fun i => w.getD i false)
  else gate.2.any (fun i => w.getD i false)

def Fires : List (Bool × List Nat) → List Bool → Prop
  | [], _ => False
  | g :: gs, w => (g.1 = true ∧ step g w = true) ∨ Fires gs (w ++ [step g w])

theorem first_and (gs : List (Bool × List Nat)) (w : List Bool)
    (t : Nat → Nat → List Bool) (same : ∀ p q, (t p q).length = w.length)
    (cover : Covers w t) (arity : ∀ g ∈ gs, g.2.length ≤ 2)
    (hit : Fires gs w) : ∃ p q, Fires gs (t p q) := by
  induction gs generalizing w t with
  | nil => exact False.elim hit
  | cons g gs ih =>
    rcases g with ⟨op, ins⟩
    by_cases h : op = true ∧ step (op, ins) w = true
    · obtain ⟨rfl, hval⟩ := h
      have bound := arity (true, ins) (by simp)
      simp only at bound
      simp [step] at hval
      cases ins with
      | nil => exact ⟨0, 0, Or.inl ⟨rfl, rfl⟩⟩
      | cons i is =>
        obtain ⟨p, hp⟩ := cover i (hval i (by simp))
        cases is with
        | nil => exact ⟨p, p, Or.inl ⟨rfl, by simpa only [step, ite_true, List.all_cons, List.all_nil, Bool.and_true] using (hp p).1⟩⟩
        | cons j js =>
          have hj : js = [] := by cases js <;> simp_all
          subst js
          obtain ⟨q, hq⟩ := cover j (hval j (by simp))
          exact ⟨p,q, Or.inl ⟨rfl, by simp only [step, ite_true, List.all_cons, List.all_nil, (hp q).1, (hq p).2, Bool.and_self]⟩⟩
    · let t' := fun p q => t p q ++ [step (op, ins) (t p q)]
      have cv : Covers (w ++ [step (op,ins) w]) t' := by
        intro i hi
        by_cases before : i < w.length
        · have old : w.getD i false = true := by simpa [List.getD, List.getElem?_append, before] using hi
          obtain ⟨p,hp⟩ := cover i old
          refine ⟨p, fun q => ?_⟩
          simpa [t', List.getD, List.getElem?_append, same, before] using hp q
        · have last : i = w.length := by
            apply Classical.byContradiction
            intro ne
            have beyond : (w ++ [step (op,ins) w]).length ≤ i := by simp; omega
            simp [List.getD,List.getElem?_eq_none beyond] at hi
          subst i
          have hv : step (op,ins) w = true := by simpa [List.getD, List.getElem?_append] using hi
          have isOr : op = false := by cases op <;> simp_all
          subst op
          have ex : ∃ k ∈ ins, w.getD k false = true := by simpa [step] using hv
          obtain ⟨k,hk,hkw⟩ := ex
          obtain ⟨p,hp⟩ := cover k hkw
          refine ⟨p, fun q => ?_⟩
          have aux (a b : Nat) (hab : (t a b).getD k false = true) : step (false,ins) (t a b) = true := by
            simpa [step] using (show ∃ j ∈ ins, (t a b).getD j false = true from ⟨k,hk,hab⟩)
          simpa [t',List.getD,List.getElem?_append,same] using And.intro (aux p q (hp q).1) (aux q p (hp q).2)
      obtain ⟨p,q,hpq⟩ := ih _ t' (by simp [t',same]) cv (by intro g hg; exact arity g (by simp [hg])) (hit.resolve_left h)
      exact ⟨p,q, Or.inr hpq⟩

def Below (w v : List Bool) : Prop := ∀ i, w.getD i false = true → v.getD i false = true

theorem step_mono (g : Bool × List Nat) {w v : List Bool} (h : Below w v) :
    step g w = true → step g v = true := by
  rcases g with ⟨b, ins⟩
  cases b
  · simp [step]
    intro i hi hv
    exact ⟨i, hi, h i hv⟩
  · simp [step]
    intro hw i hi
    exact h i (hw i hi)

theorem fires_mono (gs : List (Bool × List Nat)) {w v : List Bool}
    (len : w.length = v.length) (le : Below w v) (hit : Fires gs w) : Fires gs v := by
  induction gs generalizing w v with
  | nil => exact False.elim hit
  | cons g gs ih =>
    obtain h | h := hit
    · exact Or.inl ⟨h.1,step_mono g le h.2⟩
    · apply Or.inr
      apply ih (by simp [len]) _ h
      intro i hi
      by_cases hk : i < w.length
      · simpa [List.getD, List.getElem?_append, ← len, hk] using le i (by
          simpa [List.getD, List.getElem?_append,hk] using hi)
      · by_cases he : i = w.length
        · subst i
          simpa [List.getD, List.getElem?_append, ← len] using step_mono g le (by
            simpa [List.getD,List.getElem?_append] using hi)
        · have beyond : (w ++ [step g w]).length ≤ i := by simp; omega
          simp [List.getD,List.getElem?_eq_none beyond] at hi

def pairMask {n : Nat} (x : Fin n → Bool) (p q : Nat) (i : Fin n) : Bool :=
  x i && (i.val == p || i.val == q)

theorem pair_witness {n : Nat} (gs : List (Bool × List Nat)) (x : Fin n → Bool)
    (arity : ∀ g ∈ gs, g.2.length ≤ 2) (hit : Fires gs (List.ofFn x)) :
    ∃ p q, Fires gs (List.ofFn (pairMask x p q)) := by
  apply first_and gs _ _ (by simp) _ arity hit
  intro i hi
  by_cases h : i < n
  · simp [List.getD,h] at hi
    exact ⟨i, fun q => by simp [pairMask,List.getD,h,hi]⟩
  · simp [List.getD,h] at hi

def edge (i j : Fin 42) : Bool :=
  decide (i.val < 21 ∧ 21 ≤ j.val ∧ (j.val + 21 - i.val) % 21 ∈ [0,5,7,17,20])

def marker (i : Fin 42) : Bool :=
  decide (i.val ∈ [0,1,2,6,8,18,24,31,33,37])

-- Translations preserve the two vertex classes. The duality reverses
-- the coordinate and exchanges points and lines, preserving incidence.
def move (k : Fin 21) (dual : Bool) (i : Fin 42) : Fin 42 :=
  let a := i.val % 21
  let b := if dual then (k.val + 21 - a) % 21 else (a + k.val) % 21
  let isLine := (decide (21 ≤ i.val)) != dual
  ⟨b + (if isLine then 21 else 0), by dsimp [b]; split <;> split <;> omega⟩

def markedAt (k : Fin 21) (d : Bool) (i : Fin 42) := marker (move k d i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cover_nonedge : ∀ i j : Fin 42, edge i j = false → edge j i = false →
    ∃ k : Fin 21, ∃ d : Bool, markedAt k d i = true ∧ markedAt k d j = true := by decide

def Independent (x : Fin 42 → Bool) : Prop :=
  ∀ i j, x i = true → x j = true → edge i j = false

theorem at_bit {n : Nat} (x : Fin n → Bool) (i : Nat) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i,h⟩ := by simp [List.getD,h]

theorem off_bit {n : Nat} (x : Fin n → Bool) (i : Nat) (h : ¬i < n) :
    (List.ofFn x).getD i false = false := by simp [List.getD,h]

theorem reduce_markers (gs : List (Bool × List Nat)) (arity : ∀ g ∈ gs, g.2.length ≤ 2)
    (x : Fin 42 → Bool) (ind : Independent x) (hit : Fires gs (List.ofFn x)) :
    ∃ k d, Fires gs (List.ofFn (markedAt k d)) := by
  classical
  by_cases hx : ∃ i, x i = true
  · obtain ⟨z,hz⟩ := hx
    let v (p : Nat) : Fin 42 := if h : p < 42 then if x ⟨p,h⟩ then ⟨p,h⟩ else z else z
    have hv (p) : x (v p) = true := by
      dsimp [v]
      split
      · split <;> assumption
      · exact hz
    have H (p q : Nat) := cover_nonedge (v p) (v q) (ind _ _ (hv _) (hv _)) (ind _ _ (hv _) (hv _))
    let k p q := (H p q).choose
    let d p q := (H p q).choose_spec.choose
    let t p q := List.ofFn (markedAt (k p q) (d p q))
    have cover : Covers (List.ofFn x) t := by
      intro i hi
      by_cases lt : i < 42
      · have bit : x ⟨i,lt⟩ = true := by simpa only [at_bit _ _ lt] using hi
        have veq : v i = ⟨i,lt⟩ := by simp [v,lt,bit]
        refine ⟨i, fun q => ?_⟩
        have l := (H i q).choose_spec.choose_spec.1
        have r := (H q i).choose_spec.choose_spec.2
        change markedAt (k i q) (d i q) (v i) = true at l
        change markedAt (k q i) (d q i) (v i) = true at r
        simpa only [t,at_bit _ _ lt,veq] using And.intro l r
      · simp only [off_bit _ _ lt, Bool.false_eq_true] at hi
    obtain ⟨p,q,hpq⟩ := first_and gs _ t (by simp [t]) cover arity hit
    exact ⟨k p q, d p q,hpq⟩
  · refine ⟨0,false, fires_mono gs (by simp) ?_ hit⟩
    intro i hi
    by_cases lt : i < 42
    · exact False.elim (hx ⟨⟨i,lt⟩,by simpa only [at_bit _ _ lt] using hi⟩)
    · simp only [off_bit _ _ lt, Bool.false_eq_true] at hi

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem all_markers_independent : ∀ k d, Independent (markedAt k d) := by
  unfold Independent
  decide

open PEqualNP.CircuitLowerBounds

def code (g : Gate) : Bool × List Nat := (match g.op with | .and => true | _ => false, g.inputs)

def actual (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def finish (gs : List Gate) (w : List Bool) := gs.foldl (fun v g => v ++ [actual g v]) w

theorem finish_pre (gs : List Gate) (w : List Bool) (i : Nat) (bound : i < w.length) :
    (finish gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (finish gs (w ++ [actual g w])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD,List.getElem?_append,bound]

def hasHit (gs : List Gate) (w : List Bool) : Prop :=
  ∃ j g, gs[j]? = some g ∧ g.op = .and ∧ (finish gs w).getD (w.length + j) false = true

def Good (g : Gate) : Prop := g.op = .and ∨ g.op = .or

theorem actual_step (g : Gate) (h : Good g) (w : List Bool) :
    actual g w = step (code g) w := by
  rcases g with ⟨op,ins⟩
  obtain rfl | rfl := h <;> simp [actual,code,step,GateOp.eval,List.all_map,List.any_map]

theorem op_and (g : Gate) : (code g).1 = true ↔ g.op = .and := by
  rcases g with ⟨op,ins⟩
  cases op <;> simp [code]

theorem hasHit_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    hasHit (g::gs) w ↔ (g.op = .and ∧ actual g w = true) ∨ hasHit gs (w ++ [actual g w]) := by
  have zero : (finish (g::gs) w).getD (w.length + 0) false = actual g w := by
    change (finish gs (w ++ [actual g w])).getD _ false = _
    rw [finish_pre _ _ _ (by simp)]
    simp [List.getD]
  have idx (j : Nat) : w.length + (j+1) = (w ++ [actual g w]).length + j := by simp; omega
  constructor
  · rintro ⟨j,g',hg,hop,hv⟩
    cases j with
    | zero =>
      simp at hg
      subst g'
      exact Or.inl ⟨hop,zero ▸ hv⟩
    | succ j => exact Or.inr ⟨j,g',hg,hop,idx j ▸ hv⟩
  · rintro (⟨hop,hv⟩ | ⟨j,g',hg,hop,hv⟩)
    · exact ⟨0,g, rfl,hop,zero.trans hv⟩
    · exact ⟨j+1,g',hg,hop,(idx j).symm ▸ hv⟩

theorem hasHit_iff (gs : List Gate) (good : ∀ g ∈ gs, Good g) (w : List Bool) :
    hasHit gs w ↔ Fires (gs.map code) w := by
  induction gs generalizing w with
  | nil => simp [hasHit,Fires]
  | cons g gs ih =>
    simp only [hasHit_cons,List.map_cons,Fires,op_and,← actual_step g (good g (by simp))]
    rw [ih (by intro h hm; exact good h (by simp [hm]))]

theorem circuit_marker_iff (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C) :
    (∃ x : Fin 42 → Bool, Independent x ∧ hasHit C.gates (List.ofFn x)) ↔
    ∃ k d, hasHit C.gates (List.ofFn (markedAt k d)) := by
  have good : ∀ g ∈ C.gates, Good g := by
    intro g hg
    exact (ok g hg).1
  constructor
  · rintro ⟨x,ind,hit⟩
    have arity : ∀ h ∈ C.gates.map code, h.2.length ≤ 2 := by
      intro h hh
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hh
      exact (ok g hg).2
    obtain ⟨k,d,ev⟩ := reduce_markers _ arity x ind ((hasHit_iff _ good _).mp hit)
    exact ⟨k,d,(hasHit_iff _ good _).mpr ev⟩
  · rintro ⟨k,d,ev⟩
    exact ⟨markedAt k d,all_markers_independent k d,ev⟩

def circuitHit (C : Circuit) (x : Fin 42 → Bool) : Prop :=
  ∃ (j : Nat) (g : Gate), C.gates[j]? = some g ∧ g.op = .and ∧
    (C.wires (List.ofFn x)).getD (42 + j) false = true

theorem hit_eq (C : Circuit) (x : Fin 42 → Bool) :
    circuitHit C x ↔ hasHit C.gates (List.ofFn x) := by
  simp only [circuitHit,hasHit,List.length_ofFn]
  rfl

theorem circuit_reduction (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C) :
    (∃ x : Fin 42 → Bool, Independent x ∧ circuitHit C x) ↔
    ∃ k d, circuitHit C (markedAt k d) := by
  simpa only [hit_eq] using circuit_marker_iff C ok


def wireMap (f : Fin 42 → Fin 42) (i : Nat) : Nat :=
  if h : i < 42 then (f ⟨i,h⟩).val else i

def remapGate (f : Fin 42 → Fin 42) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (wireMap f)⟩

def remap (C : Circuit) (f : Fin 42 → Fin 42) : Circuit :=
  ⟨C.gates.map (remapGate f),wireMap f C.output⟩

theorem mapped_actual (f : Fin 42 → Fin 42) (g : Gate) (u v : List Bool)
    (rel : ∀ i, u.getD i false = v.getD (wireMap f i) false) :
    actual g u = actual (remapGate f g) v := by
  simp only [actual,remapGate,List.map_map]
  congr 1
  exact List.map_congr_left (fun i _ => rel i)

theorem snoc_read (u : List Bool) (z : Bool) (i : Nat) :
    (u ++ [z]).getD i false = if i = u.length then z else u.getD i false := by
  by_cases before : i < u.length
  · simp [List.getD,List.getElem?_append,before, Nat.ne_of_lt before]
  · by_cases eq : i = u.length
    · subst i; simp [List.getD,List.getElem?_append]
    · have beyond : (u ++ [z]).length ≤ i := by simp; omega
      simp [List.getD, List.getElem?_eq_none beyond, List.getElem?_eq_none (Nat.le_of_not_lt before),eq]

theorem finish_map (gs : List Gate) (f : Fin 42 → Fin 42) (u v : List Bool)
    (len : u.length = v.length) (base : 42 ≤ u.length)
    (rel : ∀ i, u.getD i false = v.getD (wireMap f i) false) (i : Nat) :
    (finish gs u).getD i false = (finish (gs.map (remapGate f)) v).getD (wireMap f i) false := by
  induction gs generalizing u v with
  | nil => exact rel i
  | cons g gs ih =>
    apply ih (u ++ [actual g u]) (v ++ [actual (remapGate f g) v]) (by simp [len]) (by simp; omega)
    intro j
    rw [snoc_read,snoc_read]
    have cond : wireMap f j = v.length ↔ j = u.length := by
      unfold wireMap
      split
      next h => have hh := (f ⟨j,h⟩).isLt; omega
      next => omega
    by_cases hj : j = u.length
    · rw [ite_eq_left hj,ite_eq_left (cond.mpr hj),mapped_actual f g u v rel]
    · rw [ite_eq_right hj,ite_eq_right (fun hh => hj (cond.mp hh)),rel j]

theorem read_map (C : Circuit) (f : Fin 42 → Fin 42) (x : Fin 42 → Bool) (i : Nat) :
    (C.wires (List.ofFn (x ∘ f))).getD i false =
      ((remap C f).wires (List.ofFn x)).getD (wireMap f i) false := by
  apply finish_map C.gates f _ _ (by simp) (by simp) _ i
  intro j
  by_cases h : j < 42
  · simp only [wireMap,dite_eq_left h,at_bit _ _ h,at_bit _ _ (f ⟨j,h⟩).isLt,Function.comp_apply]
  · simp only [wireMap,dite_eq_right h,off_bit _ _ h]

theorem hit_map (C : Circuit) (f : Fin 42 → Fin 42) (x : Fin 42 → Bool)
    (h : circuitHit C (x ∘ f)) : circuitHit (remap C f) x := by
  obtain ⟨j,g,hg,hop,hv⟩ := h
  refine ⟨j,remapGate f g,?_,hop,?_⟩
  · simp [remap,List.getElem?_map,hg]
  · rw [read_map] at hv
    simpa only [wireMap, dite_eq_right (show ¬42 + j < 42 by omega)] using hv

def SymEdge (i j : Fin 42) := edge i j || edge j i

def IsGeom (f : Fin 42 → Fin 42) : Prop :=
  Function.Surjective f ∧ ∀ i j, SymEdge (f i) (f j) = SymEdge i j

set_option maxRecDepth 10000 in
theorem geom_start (d : Bool) : IsGeom (move 0 d) := by
  cases d <;> unfold IsGeom Function.Surjective <;> decide

set_option maxRecDepth 10000 in
theorem geom_gen : IsGeom (move 1 false) := by
  unfold IsGeom Function.Surjective
  decide

set_option maxRecDepth 10000 in
theorem move_next : ∀ (k : Fin 20) (d : Bool) (i : Fin 42),
    move ⟨k.val + 1,by omega⟩ d i = move 1 false (move ⟨k.val, by omega⟩ d i) := by decide

theorem geom (k : Fin 21) (d : Bool) : IsGeom (move k d) := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => exact geom_start d
  | succ n ih =>
    have kn : n < 20 := by omega
    obtain ⟨onto, adj⟩ := ih (by omega)
    obtain ⟨ogen, agen⟩ := geom_gen
    constructor
    · intro j
      obtain ⟨a,rfl⟩ := ogen j
      obtain ⟨b,rfl⟩ := onto a
      exact ⟨b,move_next ⟨n,kn⟩ d b⟩
    · intro i j
      rw [move_next ⟨n,kn⟩ d i,move_next ⟨n,kn⟩ d j,agen,adj]

def AcceptsEdge (x : Fin 42 → Bool) : Prop :=
  ∃ i j, edge i j = true ∧ x i = true ∧ x j = true

theorem accepts_sym (x : Fin 42 → Bool) :
    AcceptsEdge x ↔ ∃ i j, SymEdge i j = true ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨i,j,e,hi,hj⟩; exact ⟨i,j,by simp [SymEdge,e],hi,hj⟩
  · rintro ⟨i,j,h,hi,hj⟩
    obtain e | e := Bool.or_eq_true_iff.mp h
    · exact ⟨i,j,e,hi,hj⟩
    · exact ⟨j,i,e,hj,hi⟩

theorem accepts_move (k : Fin 21) (d : Bool) (x : Fin 42 → Bool) :
    AcceptsEdge (x ∘ move k d) ↔ AcceptsEdge x := by
  rw [accepts_sym,accepts_sym]
  obtain ⟨onto,adj⟩ := geom k d
  constructor
  · rintro ⟨i,j,e,hi,hj⟩
    exact ⟨_,_,(adj i j).trans e,hi,hj⟩
  · rintro ⟨a,b,e,ha,hb⟩
    obtain ⟨i,rfl⟩ := onto a
    obtain ⟨j,rfl⟩ := onto b
    exact ⟨i,j,(adj i j).symm.trans e,ha,hb⟩

def Computes (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ AcceptsEdge x

theorem normalize_witness (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (exactFn : Computes C) (x : Fin 42 → Bool) (ind : Independent x) (hit : circuitHit C x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
      Computes D ∧ circuitHit D marker := by
  obtain ⟨k,d,hm⟩ := (circuit_reduction C ok).mp ⟨x,ind,hit⟩
  refine ⟨remap C (move k d), ?_, by simp [Circuit.size,remap], ?_, hit_map _ _ marker hm⟩
  · intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    exact ⟨(ok g' hg').1,by simpa [remapGate] using (ok g' hg').2⟩
  · intro y
    have h := read_map C (move k d) y C.output
    change C.eval (List.ofFn (y ∘ move k d)) = (remap C (move k d)).eval (List.ofFn y) at h
    rw [← h,exactFn,accepts_move]

def extend (C : Circuit) : Circuit := ⟨C.gates ++ [⟨.and, []⟩], C.output⟩

theorem finish_length (gs : List Gate) (w : List Bool) :
    (finish gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [finish]
  | cons g gs ih =>
    change (finish gs (w ++ [actual g w])).length = _
    rw [ih]
    simp; omega

theorem extend_wires (C : Circuit) (w : List Bool) :
    (extend C).wires w = C.wires w ++ [true] := by
  simp [extend,Circuit.wires,List.foldl_append,GateOp.eval]

theorem output_in_range (C : Circuit) (exactFn : Computes C) :
    C.output < 42 + C.size := by
  have yes : AcceptsEdge (fun _ => true) := ⟨0,21,by decide,rfl,rfl⟩
  have h := (exactFn _).mpr yes
  by_contra bad
  have len := finish_length C.gates (List.ofFn (fun _ : Fin 42 => true))
  change (C.wires _).length = _ at len
  simp only [List.length_ofFn] at len
  have oob : (C.wires (List.ofFn (fun _ : Fin 42 => true))).length ≤ C.output := by
    rw [len]; exact Nat.le_of_not_lt bad
  simp only [Circuit.eval,List.getD_eq_getElem?_getD,List.getElem?_eq_none oob,Option.getD_none, Bool.false_eq_true] at h

theorem extend_correct (C : Circuit) (exactFn : Computes C) : Computes (extend C) := by
  intro x
  have len := finish_length C.gates (List.ofFn x)
  change (C.wires _).length = _ at len
  have lt : C.output < (C.wires (List.ofFn x)).length := by
    rw [len,List.length_ofFn]; exact output_in_range C exactFn
  have eq : (extend C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
    change ((extend C).wires (List.ofFn x)).getD C.output false = _
    rw [extend_wires,snoc_read,ite_eq_right (Nat.ne_of_lt lt)]
    rfl
  rw [eq]; exact exactFn x

theorem extend_hit (C : Circuit) : circuitHit (extend C) marker := by
  refine ⟨C.gates.length,⟨.and,[]⟩,?_,rfl,?_⟩
  · simp [extend]
  · have len := finish_length C.gates (List.ofFn marker)
    change (C.wires _).length = _ at len
    simp only [List.length_ofFn] at len
    rw [extend_wires,snoc_read,ite_eq_left len.symm]

theorem extend_ok (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (extend C) := by
  intro g hg
  simp only [extend,List.mem_append,List.mem_singleton] at hg
  obtain hg | rfl := hg
  · exact ok g hg
  · simp

def Posted : Prop :=
  ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true))

def MarkedExample : Prop :=
  ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ Computes C ∧ circuitHit C marker

theorem posted_iff : Posted ↔ MarkedExample := by
  classical
  unfold Posted MarkedExample
  push Not
  constructor
  · rintro ⟨C,ok,sz,hit,allX⟩
    refine ⟨C,ok,sz,?_,hit⟩
    intro x
    simpa only [AcceptsEdge,edge,decide_eq_true_eq] using allX x
  · rintro ⟨C,ok,sz,allX,hit⟩
    refine ⟨C,ok,sz,hit,?_⟩
    intro x
    simpa only [AcceptsEdge,edge,decide_eq_true_eq] using allX x

theorem size_123_suffices (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (sz : C.size ≤ 123) (correct : Computes C) : Posted := by
  refine posted_iff.mpr ⟨extend C,extend_ok C ok,?_,extend_correct C correct,extend_hit C⟩
  simp only [Circuit.size,extend,List.length_append,List.length_singleton]
  change C.size + 1 ≤ 124
  omega

theorem exact_alternatives : Posted ↔
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 123 ∧ Computes C) ∨
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 124 ∧ Computes C ∧
       ∃ x, Independent x ∧ circuitHit C x) := by
  constructor
  · intro h
    obtain ⟨C,ok,sz,fn,hit⟩ := posted_iff.mp h
    by_cases small : C.size ≤ 123
    · exact Or.inl ⟨C,ok,small,fn⟩
    · have indep : Independent marker := by
        change ∀ i j : Fin 42, marker i = true → marker j = true → edge i j = false
        decide
      exact Or.inr ⟨C,ok,by omega,fn,marker,indep,hit⟩
  · rintro (⟨C,ok,sz,fn⟩ | ⟨C,ok,sz,fn,x,ind,hit⟩)
    · exact size_123_suffices C ok sz fn
    · obtain ⟨D,okD,ds,fnD,hitD⟩ := normalize_witness C ok fn x ind hit
      exact posted_iff.mpr ⟨D,okD,by omega,fnD,hitD⟩

-- Each of the 42 tests has a pair of inputs found in no other test.
-- A circuit consisting of their conjunction shows that dropping this test
-- loses the ability to detect all conjunctions on independent inputs.
def privateLeft (k : Fin 21) (d : Bool) : Fin 42 :=
  if d then ⟨21 + k.val,by omega⟩ else ⟨(21-k.val)%21,by omega⟩

def privateRight (k : Fin 21) (d : Bool) : Fin 42 :=
  if d then ⟨21 + (k.val+3)%21,by omega⟩ else ⟨(39-k.val)%21,by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem unique_test : ∀ (k : Fin 21) (d : Bool) (k' : Fin 21) (d' : Bool),
    (markedAt k' d' (privateLeft k d) = true ∧ markedAt k' d' (privateRight k d) = true)
      ↔ (k' = k ∧ d' = d) := by decide

end MarkedWitness

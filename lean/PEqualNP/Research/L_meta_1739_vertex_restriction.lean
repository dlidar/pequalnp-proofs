import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L106

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Research.VertexRestriction

-- A zero restriction eliminates every gate with a certified false operand.
-- The construction keeps the original arity and also handles out-of-range reads.
theorem eliminate_zero_readers {n : ℕ} (v : Fin n) (C : Circuit) (hm : Monotone2 C)
    (zero : ℕ → Bool)
    (sound : ∀ (x : Fin n → Bool) i, zero i = true →
      (C.wires (List.ofFn (Function.update x v false))).getD i false = false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + (C.gates.countP fun g => g.inputs.any zero) = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        C.eval (List.ofFn (Function.update x v false)) := by
  classical
  let B := n + C.size
  let hit (g : Gate) := g.inputs.any zero
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (x : List Bool) := gs.foldl step x
  have len (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step x g)).length = _
      rw [ih]; simp [step]; omega
  have snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases lt : i < w.length
    · rw [List.getD_append _ _ _ _ lt,ite_eq_right (Nat.ne_of_lt lt)]
    · by_cases eq : i = w.length
      · subst i; simp [List.getD]
      · have o : (w ++ [b]).length ≤ i := by simp; omega
        rw [List.getD_eq_default _ _ o,ite_eq_right eq,List.getD_eq_default _ _ (by omega)]
  let good (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
  have prefixRun (gs : List Gate) (w : List Bool) : w <+: run gs w := by
    induction gs generalizing w with
    | nil => exact List.prefix_refl _
    | cons g gs ih => exact (List.prefix_append w _).trans (ih (step w g))
  have construct (gs : List Gate) (pref : gs <+: C.gates) (bound : gs.length ≤ C.size) (ok : ∀ g ∈ gs, good g) :
      ∃ (ds : List Gate) (f : ℕ → ℕ), (∀ g ∈ ds, good g) ∧
        ds.length + gs.countP hit = gs.length ∧ f v = B ∧
        (∀ i, f i < n + ds.length ∨ f i = B) ∧
        ∀ (x : Fin n → Bool) i, (run gs (List.ofFn (Function.update x v false))).getD i false =
          (run ds (List.ofFn x)).getD (f i) false := by
    induction gs using List.reverseRecOn with
    | nil =>
      let f (i : ℕ) := if i < n ∧ i ≠ v.val then i else B
      refine ⟨[],f,by simp,by simp,by simp [f],?_,?_⟩
      · intro i; dsimp [f]; split <;> simp_all
      · intro x i
        change (List.ofFn (Function.update x v false)).getD i false = (List.ofFn x).getD (f i) false
        have off : (List.ofFn x).getD B false = false := List.getD_eq_default _ _ (by simp [B])
        by_cases h : i < n
        · by_cases e : i = v.val
          · subst i; rw [show f v = B by simp [f],off,List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
            simp
          · rw [show f i = i by simp [f,h,e],List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn,List.getElem_ofFn]
            exact Function.update_of_ne (fun eq => e (congrArg Fin.val eq)) _ _
        · rw [show f i = B by simp [f,h],off,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]
    | append_singleton gs g ih =>
      have bd : gs.length + 1 ≤ C.size := by simpa using bound
      obtain ⟨ds,f,dok,sz,fv,range,rel⟩ := ih ((List.prefix_append gs [g]).trans pref) (by omega) (fun a ha => ok a (List.mem_append_left _ ha))
      obtain ⟨op,arity⟩ := ok g (by simp)
      let old := n + gs.length
      let fresh := n + ds.length
      have lower : fresh < B := by dsimp [fresh,B]; omega
      have nv : v.val ≠ old := by have := v.isLt; dsimp [old]; omega
      let A (x : Fin n → Bool) := run gs (List.ofFn (Function.update x v false))
      let V (x : Fin n → Bool) := run ds (List.ofFn x)
      have al x : (A x).length = old := by simp [A,len,old]
      have vl x : (V x).length = fresh := by simp [V,len,fresh]
      have av (x : Fin n → Bool) (i : ℕ) (hi : zero i = true) :
          (A x).getD i false = false := by
        by_cases lt : i < (A x).length
        · obtain ⟨tail, ht⟩ := (List.prefix_append gs [g]).trans pref
          have full := sound x i hi
          change (run C.gates _).getD i false = false at full
          rw [← ht] at full
          change ((gs ++ tail).foldl step _).getD i false = false at full
          rw [List.foldl_append] at full
          obtain ⟨rest, hr⟩ := prefixRun tail (A x)
          change (run tail (A x)).getD i false = false at full
          rwa [← hr,List.getD_append _ _ _ _ lt] at full
        · exact List.getD_eq_default _ _ (by omega)
      by_cases h : g.inputs.any zero = true
      · let pick := (g.inputs.filter (fun i => !(zero i))).head?
        let z : ℕ := if g.op = .and then B else (pick.map f).getD B
        have rz : z < fresh ∨ z = B := by
          dsimp only [z]; split
          · exact Or.inr rfl
          · cases hp : pick with
            | none => exact Or.inr rfl
            | some a => exact range a
        let t (i : ℕ) := if i = old then z else f i
        refine ⟨ds,t,dok,?_,by simpa [t,nv] using fv,?_,?_⟩
        · simp [List.countP_append,hit,h]; dsimp [hit] at sz; omega
        · intro i; dsimp [t]; split <;> first | exact rz | exact range i
        · intro x i
          have bfalse : (V x).getD B false = false := List.getD_eq_default _ _ (by rw [vl]; omega)
          have eqg : g.op.eval (g.inputs.map fun a => (A x).getD a false) = (V x).getD z false := by
            rcases op with hand|hor
            · rw [hand]; change (g.inputs.map _).all id = _
              rw [show z = B by simp [z,hand],bfalse]
              cases e : (g.inputs.map (fun a => (A x).getD a false)).all id with
              | false => rfl
              | true =>
                obtain ⟨a, mem, za⟩ := List.any_eq_true.mp h
                have all := List.all_eq_true.mp e ((A x).getD a false) (List.mem_map.mpr ⟨a,mem,rfl⟩)
                rw [av x a za] at all
                contradiction
            · have zz : z = (pick.map f).getD B := by simp [z,hor]
              rw [hor,zz]; change (g.inputs.map _).any id = _
              cases gi : g.inputs with
              | nil => simp [gi] at h
              | cons a tail =>
                cases tail with
                | nil =>
                  have za : zero a = true := by simpa [gi] using h
                  simp [pick,gi,za,av x a za,bfalse,-List.getD_eq_getElem?_getD]
                | cons b rest =>
                  have emp : rest = [] := by rw [gi] at arity; simpa using arity
                  subst rest
                  cases ha : zero a <;> cases hb : zero b
                  · simp [gi,ha,hb] at h
                  · simpa [pick,gi,ha,hb,av x b hb,-List.getD_eq_getElem?_getD] using rel x a
                  · simpa [pick,gi,ha,hb,av x a ha,-List.getD_eq_getElem?_getD] using rel x b
                  · simp [pick,gi,ha,hb,av x a ha,av x b hb,bfalse,-List.getD_eq_getElem?_getD]
          change ((gs ++ [g]).foldl step _).getD i false = (V x).getD (t i) false
          rw [List.foldl_append]; change (A x ++ [_]).getD i false = _
          rw [snoc,al]
          by_cases eq : i = old
          · simpa only [t,ite_eq_left eq] using eqg
          · simpa only [t,ite_eq_right eq] using rel x i
      · let g' : Gate := ⟨g.op,g.inputs.map f⟩
        let t (i : ℕ) := if i = old then fresh else f i
        refine ⟨ds ++ [g'],t,?_,?_,by simpa [t,nv] using fv,?_,?_⟩
        · intro a ha; rcases List.mem_append.mp ha with ha|ha
          · exact dok a ha
          · obtain rfl := List.mem_singleton.mp ha
            exact ⟨op,by simpa [g'] using arity⟩
        · simp [List.countP_append,hit,h]; dsimp [hit] at sz; omega
        · intro i; simp only [List.length_append,List.length_singleton]
          by_cases eq : i = old
          · exact Or.inl (by simp [t,eq,fresh])
          · rw [show t i = f i by simp [t,eq]]
            rcases range i with lt|same
            · exact Or.inl (by omega)
            · exact Or.inr same
        · intro x i
          have eqg : g.op.eval (g.inputs.map fun a => (A x).getD a false) =
              g'.op.eval (g'.inputs.map fun a => (V x).getD a false) := by
            simp only [g',List.map_map]; exact congrArg g.op.eval (List.map_congr_left (fun a _ => rel x a))
          change ((gs ++ [g]).foldl step _).getD i false = ((ds ++ [g']).foldl step _).getD (t i) false
          rw [List.foldl_append,List.foldl_append]
          change (A x ++ [_]).getD i false = (V x ++ [_]).getD (t i) false
          rw [snoc,snoc,al,vl,eqg]
          by_cases eq : i = old
          · simp [t,eq,V,run]
          · have ne : f i ≠ fresh := by rcases range i with lt|hb <;> dsimp [fresh] at * <;> omega
            simpa only [t,ite_eq_right eq,ite_eq_right ne] using rel x i
  obtain ⟨ds,f,ok,sz,_,_,val⟩ := construct C.gates (List.prefix_refl _) (le_refl _) hm
  exact ⟨⟨ds,f C.output⟩,ok,sz,fun x => (val x C.output).symm⟩

theorem eliminate_readers {n : ℕ} (v : Fin n) (C : Circuit) (hm : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + (C.gates.countP fun g => decide (v.val ∈ g.inputs)) = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        C.eval (List.ofFn (Function.update x v false)) := by
  let zero (i : ℕ) := decide (v.val = i)
  have sound (x : Fin n → Bool) (i : ℕ) (hi : zero i = true) :
      (C.wires (List.ofFn (Function.update x v false))).getD i false = false := by
    have eq : v.val = i := of_decide_eq_true hi
    subst i
    let w := List.ofFn (Function.update x v false)
    let step (l : List Bool) (g : Gate) := l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]
    have ext (gs : List Gate) (l : List Bool) : l <+: gs.foldl step l := by
      induction gs generalizing l with
      | nil => exact List.prefix_refl _
      | cons g gs ih => exact (List.prefix_append l _).trans (ih (step l g))
    obtain ⟨t,eq⟩ := ext C.gates w
    change (C.gates.foldl step w).getD v.val false = false
    rw [← eq,List.getD_append _ _ _ _ (by simp [w]), List.getD_eq_getElem _ _ (by simp [w])]
    simp [w]
  have same (g : Gate) : g.inputs.any zero = decide (v.val ∈ g.inputs) := by
    apply Bool.eq_iff_iff.mpr
    simp [zero,List.any_eq_true]
  simpa only [same] using eliminate_zero_readers v C hm zero sound

-- Isolating a vertex in an edge function is exactly a zero restriction.
def ComputesEdge {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

theorem computes_restricted {n : ℕ} (v : Fin n) {C D : Circuit} {G : SimpleGraph (Fin n)}
    (hc : ComputesEdge C G)
    (val : ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update x v false))) :
    ComputesEdge D (G.deleteIncidenceSet v) := by
  intro x
  rw [val, hc]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have av : a ≠ v := by rintro rfl; simp at ha
    have bv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab,av,bv⟩,
      by simpa [Function.update_of_ne av] using ha,
      by simpa [Function.update_of_ne bv] using hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    obtain ⟨hab,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp edge
    exact ⟨a,b,hab,by simpa [Function.update_of_ne av] using ha,
      by simpa [Function.update_of_ne bv] using hb⟩

-- An induction on edges can discharge a vertex if the gates removed pay for
-- the lost edges and any decrease in the minimum cover size.
theorem lower_bound_step {n k t : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (v : Fin n) (hm : Monotone2 C) (hc : ComputesEdge C G) (zero : ℕ → Bool)
    (sound : ∀ (x : Fin n → Bool) i, zero i = true →
      (C.wires (List.ofFn (Function.update x v false))).getD i false = false)
    (budget : (G.incidenceSet v).ncard + k ≤
      (C.gates.countP fun g => g.inputs.any zero) + t)
    (ih : ∀ D : Circuit, Monotone2 D → ComputesEdge D (G.deleteIncidenceSet v) →
      (G.deleteIncidenceSet v).edgeSet.ncard + t ≤ D.size + 1) :
    G.edgeSet.ncard + k ≤ C.size + 1 := by
  obtain ⟨D, mono, size, val⟩ := eliminate_zero_readers v C hm zero sound
  have smaller := ih D mono (computes_restricted v hc val)
  have edges := Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v)
  rw [← G.edgeSet_deleteIncidenceSet v] at edges
  omega

-- On the five-cycle the direct-reader budget fails at every vertex of this
-- seven-gate circuit, even though the desired lower bound holds with equality.
def pentagon : Circuit :=
  ⟨[⟨.or,[1,4]⟩, ⟨.and,[0,5]⟩, ⟨.or,[1,3]⟩, ⟨.and,[2,7]⟩,
    ⟨.and,[3,4]⟩, ⟨.or,[6,8]⟩, ⟨.or,[10,9]⟩], 11⟩

def MinimumCover {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = k) ∧
  ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → k ≤ S.card

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem pentagon_obstruction :
    Monotone2 pentagon ∧ pentagon.size = 7 ∧ ComputesEdge pentagon (SimpleGraph.cycleGraph 5) ∧
    MinimumCover (SimpleGraph.cycleGraph 5) 3 ∧
    ∀ v : Fin 5, MinimumCover ((SimpleGraph.cycleGraph 5).deleteIncidenceSet v) 2 ∧
      ((SimpleGraph.cycleGraph 5).incidenceSet v).ncard + 3 >
        (pentagon.gates.countP fun g => decide (v.val ∈ g.inputs)) + 2 := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · simp [Monotone2,pentagon]
  · unfold ComputesEdge; decide
  · unfold MinimumCover CoverPromise.IsVertexCover; decide
  · intro v
    rw [SimpleGraph.ncard_incidenceSet]
    unfold MinimumCover CoverPromise.IsVertexCover
    simp only [SimpleGraph.deleteIncidenceSet_adj]
    decide +revert

-- Vertex 3 shows why a downstream false wire matters. Its AND with vertex 4
-- is wire 9. Marking both wires charges three gates and leaves exactly four.
theorem pentagon_three_gate_saving :
    ∃ D : Circuit, Monotone2 D ∧ D.size = 4 ∧
      ComputesEdge D ((SimpleGraph.cycleGraph 5).deleteIncidenceSet 3) := by
  let zero (i : ℕ) := decide (i = 3 ∨ i = 9)
  have sound (x : Fin 5 → Bool) (i : ℕ) (hi : zero i = true) :
      (pentagon.wires (List.ofFn (Function.update x 3 false))).getD i false = false := by
    obtain h | h := of_decide_eq_true hi <;> subst i <;> decide +revert
  have ⟨D,mono,size,val⟩ := eliminate_zero_readers (3 : Fin 5) pentagon
    pentagon_obstruction.1 zero sound
  have count : (pentagon.gates.countP fun g => g.inputs.any zero) = 3 := by decide
  rw [count, pentagon_obstruction.2.1] at size
  exact ⟨D, mono, by omega, computes_restricted 3 pentagon_obstruction.2.2.1 val⟩

-- Factoring the six-cycle at alternate vertices uses eight gates. Even a
-- certificate containing every forced-false wire pays for only two gates at
-- any one vertex. Deleting that vertex loses two edges and one cover vertex.
def hexagon : Circuit :=
  ⟨[⟨.or,[1,5]⟩, ⟨.and,[0,6]⟩, ⟨.or,[1,3]⟩, ⟨.and,[2,8]⟩,
    ⟨.or,[3,5]⟩, ⟨.and,[4,10]⟩, ⟨.or,[7,9]⟩, ⟨.or,[12,11]⟩], 13⟩

def topZeros (C : Circuit) {n : ℕ} (v : Fin n) (i : ℕ) : Bool :=
  !(C.wires (List.ofFn (Function.update (fun _ => true) v false))).getD i false

theorem reader_bound_at_top {n : ℕ} (C : Circuit) (v : Fin n) (zero : ℕ → Bool)
    (sound : ∀ (x : Fin n → Bool) i, zero i = true →
      (C.wires (List.ofFn (Function.update x v false))).getD i false = false) :
    (C.gates.countP fun g => g.inputs.any zero) ≤
      (C.gates.countP fun g => g.inputs.any (topZeros C v)) := by
  apply List.countP_mono_left
  intro g _
  simp only [List.any_eq_true]
  rintro ⟨i, hi, z⟩
  exact ⟨i, hi, by unfold topZeros; rw [sound (fun _ => true) i z]; rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem hexagon_obstruction :
    Monotone2 hexagon ∧ hexagon.size = 8 ∧ ComputesEdge hexagon (SimpleGraph.cycleGraph 6) ∧
    MinimumCover (SimpleGraph.cycleGraph 6) 3 ∧
    ∀ v : Fin 6, MinimumCover ((SimpleGraph.cycleGraph 6).deleteIncidenceSet v) 2 ∧
      ((SimpleGraph.cycleGraph 6).incidenceSet v).ncard = 2 ∧
      ∀ zero : ℕ → Bool, (∀ (x : Fin 6 → Bool) i, zero i = true →
        (hexagon.wires (List.ofFn (Function.update x v false))).getD i false = false) →
        (hexagon.gates.countP fun g => g.inputs.any zero) ≤ 2 := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · simp [Monotone2,hexagon]
  · unfold ComputesEdge; decide
  · unfold MinimumCover CoverPromise.IsVertexCover; decide
  · intro v
    refine ⟨?_,?_,?_⟩
    · unfold MinimumCover CoverPromise.IsVertexCover
      simp only [SimpleGraph.deleteIncidenceSet_adj]
      decide +revert
    · rw [SimpleGraph.ncard_incidenceSet]; decide +revert
    · intro zero sound
      apply (reader_bound_at_top hexagon v zero sound).trans
      clear zero sound
      decide +revert

-- Fixing a vertex to true makes its neighbors singleton terms. Edges meeting
-- those neighbors are absorbed, leaving only edges outside the closed neighborhood.
theorem positive_restriction {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hc : ComputesEdge C G) (v : Fin n) (x : Fin n → Bool) :
    C.eval (List.ofFn (Function.update x v true)) = true ↔
      (∃ u, G.Adj v u ∧ x u = true) ∨
      (∃ a b, G.Adj a b ∧ a ≠ v ∧ b ≠ v ∧ ¬ G.Adj v a ∧ ¬ G.Adj v b ∧
        x a = true ∧ x b = true) := by
  rw [hc]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    by_cases av : a = v
    · subst a
      exact Or.inl ⟨b,edge,by simpa [Function.update_of_ne edge.ne.symm] using hb⟩
    by_cases bv : b = v
    · subst b
      exact Or.inl ⟨a,edge.symm,by simpa [Function.update_of_ne av] using ha⟩
    rw [Function.update_of_ne av] at ha
    rw [Function.update_of_ne bv] at hb
    by_cases na : G.Adj v a
    · exact Or.inl ⟨a,na,ha⟩
    by_cases nb : G.Adj v b
    · exact Or.inl ⟨b,nb,hb⟩
    exact Or.inr ⟨a,b,edge,av,bv,na,nb,ha,hb⟩
  · rintro (⟨u,edge,h⟩ | ⟨a,b,edge,av,bv,_,_,ha,hb⟩)
    · exact ⟨v,u,edge,by simp,by simpa [Function.update_of_ne edge.ne.symm] using h⟩
    · exact ⟨a,b,edge,by simpa [Function.update_of_ne av] using ha,
        by simpa [Function.update_of_ne bv] using hb⟩

-- Fixing vertex 1 to true in the same six-cycle removes four gates.
theorem hexagon_positive_saving :
    ∃ D : Circuit, Monotone2 D ∧ D.size = 4 ∧ ∀ x : Fin 6 → Bool,
      D.eval (List.ofFn x) = hexagon.eval (List.ofFn (Function.update x 1 true)) := by
  let D : Circuit :=
    ⟨[⟨.or,[3,5]⟩, ⟨.and,[4,6]⟩, ⟨.or,[0,2]⟩, ⟨.or,[7,8]⟩],9⟩
  refine ⟨D,?_,rfl,?_⟩
  · simp [Monotone2,D]
  · decide

-- The project's cycle lower bound certifies that the obstruction already
-- occurs in a minimum-size circuit.
theorem hexagon_minimal : IsMinimalMonoCircuit 6 hexagon := by
  refine ⟨hexagon_obstruction.1, ?_⟩
  intro D mono eq
  have binary : FanInTwo D := by
    intro g mem
    obtain ⟨ops, arity⟩ := mono g mem
    refine ⟨?_,arity⟩
    rcases ops with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have val : ∀ x : Fin 6 → Bool, hexagon.eval (List.ofFn x) =
      decide (∃ i j : Fin 6, (i.val + 1) % 6 = j.val ∧ x i = true ∧ x j = true) := by decide
  have bound := (L106 6 D.size (by decide)).mp
    ⟨D,binary,le_rfl,fun x => (congrFun eq x).trans (val x)⟩
  rw [hexagon_obstruction.2.1]
  omega

end PEqualNP.Research.VertexRestriction

import PEqualNP.Research.ReaderBudget
import PEqualNP.Defs.MetaComplexityMinimal
namespace PEqualNP.Research.MinimumReaderBudget
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.ReaderBudget
-- Wire deletion and index shifting are adapted from the upstream proof L_meta_931.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def shiftIdx (k i : ℕ) : ℕ := if i < k then i else i - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx k)⟩

def deleteGate (n : ℕ) (C : Circuit) (p : ℕ) : Circuit :=
  ⟨C.gates.take p ++ (C.gates.drop (p + 1)).map (shiftGate (n + p)), shiftIdx (n + p) C.output⟩

theorem getD_del_eq (u v : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ u.length) :
    (u ++ b :: v).getD i false = (u ++ v).getD (shiftIdx u.length i) false := by
  simp only [shiftIdx]
  by_cases hlt : i < u.length
  · rw [ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · rw [ite_eq_right hlt]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    have hsub : i - u.length = (i - 1 - u.length) + 1 := by omega
    rw [hsub, List.getElem?_cons_succ]

theorem wiresFrom_delete_aux (u : List Bool) (b : Bool) (rest : List Gate) :
    ∀ v : List Bool, (∀ g ∈ rest, ∀ i ∈ g.inputs, i ≠ u.length) →
      ∃ v' : List Bool,
        wiresFrom rest (u ++ b :: v) = u ++ b :: v' ∧
        wiresFrom (rest.map (shiftGate u.length)) (u ++ v) = u ++ v' := by
  induction rest with
  | nil =>
    intro v _
    exact ⟨v, rfl, rfl⟩
  | cons g gs ih =>
    intro v hall
    have hg := hall g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, ∀ i ∈ g'.inputs, i ≠ u.length :=
      fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')
    have hmap : g.inputs.map (fun i => (u ++ b :: v).getD i false) =
        (g.inputs.map (shiftIdx u.length)).map (fun i => (u ++ v).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact getD_del_eq u v b i (hg i hi)
    have hev : g.op.eval (g.inputs.map fun i => (u ++ b :: v).getD i false) =
        (shiftGate u.length g).op.eval ((shiftGate u.length g).inputs.map fun i => (u ++ v).getD i false) := by
      simp only [shiftGate, hmap]
    let c := g.op.eval (g.inputs.map fun i => (u ++ b :: v).getD i false)
    obtain ⟨v', h1, h2⟩ := ih (v ++ [c]) hgs
    refine ⟨v', ?_, ?_⟩
    · change wiresFrom gs ((u ++ b :: v) ++ [c]) = u ++ b :: v'
      simpa [List.append_assoc] using h1
    · change wiresFrom (gs.map (shiftGate u.length))
        ((u ++ v) ++ [(shiftGate u.length g).op.eval ((shiftGate u.length g).inputs.map fun i => (u ++ v).getD i false)]) = u ++ v'
      rw [← hev]
      simpa [c, List.append_assoc] using h2

theorem deleteGate_spec {n : ℕ} (C : Circuit) (hM : FanInTwo C) (p : ℕ) (hp : p < C.gates.length)
    (hout : C.output ≠ n + p)
    (hunused : ∀ g ∈ C.gates.drop (p + 1), ∀ i ∈ g.inputs, i ≠ n + p) :
    FanInTwo (deleteGate n C p) ∧
    (deleteGate n C p).size + 1 = C.size ∧
    ∀ x : Fin n → Bool, (deleteGate n C p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [deleteGate, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hM g (List.mem_of_mem_take h1)
    · obtain ⟨hop, hlen⟩ := hM g0 (List.mem_of_mem_drop hg0)
      exact ⟨hop, by simpa [shiftGate] using hlen⟩
  · simp only [Circuit.size, deleteGate, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega
  · intro x
    have hsplit : C.gates = (C.gates.take p ++ [C.gates[p]]) ++ C.gates.drop (p + 1) := by
      conv_lhs => rw [← List.take_append_drop (p + 1) C.gates]
      rw [List.take_succ_eq_append_getElem hp]
    let u := wiresFrom (C.gates.take p) (List.ofFn x)
    have hu : u.length = n + p := by
      simp [u, length_wiresFrom, List.length_take, Nat.min_eq_left hp.le]
    let b := C.gates[p].op.eval (C.gates[p].inputs.map fun i => u.getD i false)
    have h1 : C.wires (List.ofFn x) = wiresFrom (C.gates.drop (p + 1)) (u ++ b :: []) := by
      change wiresFrom C.gates (List.ofFn x) = _
      conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append]
      rfl
    have h2 : (deleteGate n C p).wires (List.ofFn x) =
        wiresFrom ((C.gates.drop (p + 1)).map (shiftGate u.length)) (u ++ []) := by
      change wiresFrom (C.gates.take p ++ (C.gates.drop (p + 1)).map (shiftGate (n + p))) (List.ofFn x) = _
      rw [wiresFrom_append, ← hu]
      simp [u]
    obtain ⟨v', hv1, hv2⟩ := wiresFrom_delete_aux u b (C.gates.drop (p + 1)) [] (by simpa [hu] using hunused)
    rw [Circuit.eval, Circuit.eval, h1, h2, hv1, hv2]
    change (u ++ v').getD (shiftIdx (n + p) C.output) false = (u ++ b :: v').getD C.output false
    rw [← hu, getD_del_eq u v' b C.output (by omega)]


def trimmedGate (g : Gate) : Gate := ⟨g.op,used g⟩
def trimmed (C : Circuit) : Circuit := ⟨C.gates.map trimmedGate,C.output⟩
theorem trim_fan (C : Circuit) (hf : FanInTwo C) : FanInTwo (trimmed C) := by
  rintro _ hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact ⟨(hf g hg).1,used_le_two g⟩
theorem trim_step (g : Gate) (w : List Bool) (ok : g.op=.and ∨ g.op=.or ∨ g.op=.not)
    (len : g.inputs.length ≤ 2) : g.op.eval ((used g).map (fun i => w.getD i false)) =
    g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  rcases ok with h|h|h
  · simp [used,h,GateOp.eval,List.take_of_length_le len]
  · simp [used,h,GateOp.eval,List.take_of_length_le len]
  · cases hi : g.inputs <;> simp [used,h,GateOp.eval,hi]
theorem trim_wires (gs : List Gate) (hf : FanInTwo ⟨gs,0⟩) (w : List Bool) :
    wiresFrom (gs.map trimmedGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,len⟩ := hf g List.mem_cons_self
    have h := trim_step g w (by simpa using op) len
    change wiresFrom (gs.map trimmedGate) (w ++ [g.op.eval ((used g).map _)]) = _
    rw [h]
    exact ih (fun t ht => hf t (List.mem_cons_of_mem _ ht)) _
theorem reads_positive {gs : List Gate} {i : Nat} {g : Gate} (hg : g ∈ gs) (hi : i ∈ used g) :
    0 < readers gs i := by
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg,by simpa using hi⟩ : g ∈ gs.filter (fun g => (used g).contains i))
theorem live_at {n : Nat} (C : Circuit) (hm : IsMinimalCircuit n C) (p : Nat)
    (hp : p<C.size) (ho : C.output ≠ n+p) : 0 < readers C.gates (n+p) := by
  by_contra! h
  let D := trimmed C
  have hs : D.size=C.size := by simp [D,trimmed,Circuit.size]
  have hd := trim_fan C hm.1
  have he (x : Fin n → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    exact congrArg (fun w : List Bool => w.getD C.output false) (trim_wires C.gates hm.1 _)
  have unused : ∀ g∈D.gates.drop (p+1), ∀ i∈g.inputs,i≠n+p := by
    intro g hg i hi eq
    have hmem : g∈D.gates := List.mem_of_mem_drop hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hmem
    exact (Nat.not_lt_of_ge h) (reads_positive ht (eq ▸ hi))
  obtain ⟨fan,sz,ev⟩ := deleteGate_spec D hd p (by change p<D.size;omega) ho unused
  have le := hm.2 (deleteGate n D p) fan (by funext x;exact (ev x).trans (he x))
  omega
theorem minimum_raw_budget {n : Nat} (C : Circuit) (hm : IsMinimalCircuit n C) :
    (∑ i ∈ range n,readers C.gates i) ≤ C.size+1 := by
  apply raw_slots
  have h : (∑ j ∈ range C.size, if n+j=C.output then 0 else 1) ≤ ∑ j ∈ range C.size,readers C.gates (n+j) := by
    apply sum_le_sum;intro j hj;split
    · omega
    · exact live_at C hm j (mem_range.mp hj) (by omega)
  have a : ((range C.size).filter (fun j => n+j=C.output)).card ≤ 1 := by
    apply card_le_one.mpr;intro x hx y hy
    have h₁ := (mem_filter.mp hx).2
    have h₂ := (mem_filter.mp hy).2
    omega
  have t := Finset.card_filter_add_card_filter_not (s:=range C.size) (p:=fun j => n+j=C.output)
  simp only [card_range] at t
  have flip (j : ℕ) : (if n+j=C.output then 0 else 1 : Nat) = (if ¬n+j=C.output then 1 else 0) := by split_ifs <;> omega
  simp only [flip, ← card_filter] at h
  omega
end PEqualNP.Research.MinimumReaderBudget

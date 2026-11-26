import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Research.Trace7368

abbrev Mask := Finset (Fin 24)
abbrev Bank := List (Set Mask)
abbrev Rule := Bool × Nat × Nat

def step (w : Bank) (g : Rule) : Bank :=
  w ++ [if g.1 then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅]

def base : Bank := List.ofFn fun i : Fin 24 => {s | i ∈ s}
def gate (g : Rule) : Gate := ⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩

noncomputable def evalAt (s : Mask) (w : Bank) : List Bool := by classical exact w.map fun a => decide (s ∈ a)

theorem get_at (s : Mask) (w : Bank) (i : Nat) :
    (evalAt s w).getD i false = true ↔ s ∈ w.getD i ∅ := by
  classical
  simp only [evalAt,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp

theorem fold_at (s : Mask) (w : Bank) (gs : List Rule) :
    evalAt s (gs.foldl step w) = (Circuit.mk (gs.map gate) 0).wires (evalAt s w) := by
  classical
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons,ih,Circuit.wires,List.map_cons]
    congr 1
    simp only [step,evalAt,List.map_append,List.map_cons,List.map_nil]
    congr 1
    rcases g with ⟨o,a,b⟩
    cases o <;> simp [gate,GateOp.eval] <;> cases w[a]? <;> cases w[b]? <;> simp

theorem compiler (gs : List Rule) (o : Fin 3 → Nat) (hd : gs.head? = some (false,0,1))
    (_ : ∀ t, o t < 24+gs.length) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧ C.gates.head? = some ⟨.or,[0,1]⟩ ∧
      C.output = o 0 ∧ ∀ (s : Mask) (i : Nat),
      (C.wires (List.ofFn fun j => decide (j ∈ s))).getD i false = true ↔ s ∈ (gs.foldl step base).getD i ∅ := by
  classical
  refine ⟨⟨gs.map gate,o 0⟩,?_,by simp [Circuit.size],?_,rfl,?_⟩
  · intro q hq
    obtain ⟨⟨o,a,b⟩,_,rfl⟩ := List.mem_map.mp hq
    cases o <;> simp [gate]
  · change (gs.map gate).head? = _
    simp [List.head?_map,hd,gate]
  · intro s i
    have hb : evalAt s base = List.ofFn fun j : Fin 24 => decide (j ∈ s) := by
      simp only [evalAt,base,List.map_ofFn]; congr 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    rw [← hb,← get_at]
    exact congrArg (fun v : List Bool => v.getD i false = true) (fold_at s base gs).symm |> Iff.of_eq

def Upper (s : Set Mask) := ∀ a ∈ s, ∀ b, a ⊆ b → b ∈ s

theorem read_upper (w : Bank) (hw : ∀ s ∈ w, Upper s) (i : Nat) : Upper (w.getD i ∅) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : w[i]? with
  | none => simp [Upper]
  | some s => exact hw s (List.mem_of_getElem? e)

theorem up_fold (gs : List Rule) (w : Bank) (hw : ∀ s ∈ w, Upper s) :
    ∀ s ∈ gs.foldl step w, Upper s := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g t ih =>
    apply ih
    intro s hs
    simp only [step,List.mem_append,List.mem_singleton] at hs
    rcases hs with h | rfl
    · exact hw s h
    · have a := read_upper w hw g.2.1
      have b := read_upper w hw g.2.2
      cases e : g.1
      · simp only [Bool.false_eq_true,ite_false]
        intro u hu v sub
        exact hu.elim (fun h => Or.inl (a _ h _ sub)) (fun h => Or.inr (b _ h _ sub))
      · simp only [ite_true]
        intro u hu v sub
        exact ⟨a _ hu.1 _ sub,b _ hu.2 _ sub⟩

theorem upward (gs : List Rule) (i : Nat) : Upper ((gs.foldl step base).getD i ∅) := by
  apply read_upper _ (up_fold gs base ?_)
  intro s h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact fun _ hx _ sub => sub hx

theorem extend (W : Set Mask) (P N : Mask → Prop) (up : Upper W)
    (pos : ∀ a, P a → (∀ b, b ⊂ a → ¬ P b) → a ∈ W)
    (neg : ∀ a, N a → (∀ b, a ⊂ b → ¬ N b) → a ∉ W) (a : Mask) :
    (P a → a ∈ W) ∧ (N a → a ∉ W) := by
  classical
  constructor
  · intro ha
    let candidates := a.powerset.filter P
    have mem : a ∈ candidates := by simp [candidates,ha]
    obtain ⟨u,hu,hm⟩ := candidates.exists_min_image Finset.card ⟨a,mem⟩
    obtain ⟨sub,hp⟩ := Finset.mem_filter.mp hu
    apply up u (pos u hp ?_) a (Finset.mem_powerset.mp sub)
    intro b hb hpb
    have bm : b ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hb.le.trans (Finset.mem_powerset.mp sub)),hpb⟩
    exact (Nat.not_lt_of_ge (hm b bm)) (Finset.card_lt_card hb)
  · intro ha yes
    let candidates := Finset.univ.filter fun b : Mask => a ⊆ b ∧ N b
    have mem : a ∈ candidates := by simp [candidates,ha]
    obtain ⟨u,hu,hm⟩ := candidates.exists_max_image Finset.card ⟨a,mem⟩
    obtain ⟨sub,hn⟩ := (Finset.mem_filter.mp hu).2
    apply neg u hn ?_ (up a yes u sub)
    intro b hb hnb
    have bm : b ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub.trans hb.le,hnb⟩
    exact (Nat.not_lt_of_ge (hm b bm)) (Finset.card_lt_card hb)
theorem exact_compile : ∀ (gs : List (Bool × ℕ × ℕ)) (o : Fin 3 → ℕ),
    gs.head? = some (false,0,1) → (∀ t, o t < 24+gs.length) →
    ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧ C.gates.head? = some ⟨.or,[0,1]⟩ ∧
      C.output = o 0 ∧ ∀ (s : Finset (Fin 24)) (i : ℕ),
      (C.wires (List.ofFn fun j => decide (j ∈ s))).getD i false = true ↔
      s ∈ (gs.foldl (fun (w : List (Set (Finset (Fin 24)))) g =>
        w ++ [ite (g.1 = true) (w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅) (w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)])
        (List.ofFn fun i : Fin 24 => {s | i ∈ s})).getD i ∅ := compiler

theorem exact_extend : ∀ (W : Set (Finset (Fin 24))) (P N : Finset (Fin 24) → Prop),
    (∀ a ∈ W, ∀ b, a ⊆ b → b ∈ W) →
    (∀ a, P a → (∀ b, b ⊂ a → ¬ P b) → a ∈ W) →
    (∀ a, N a → (∀ b, a ⊂ b → ¬ N b) → a ∉ W) →
    ∀ a, (P a → a ∈ W) ∧ (N a → a ∉ W) := extend

theorem exact_up : ∀ (gs : List (Bool × ℕ × ℕ)) (i : ℕ),
      let w := gs.foldl (fun (w : List (Set (Finset (Fin 24)))) g =>
        w ++ [ite (g.1 = true) (w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅) (w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)])
        (List.ofFn fun i : Fin 24 => {s | i ∈ s});
      ∀ a ∈ w.getD i ∅, ∀ b, a ⊆ b → b ∈ w.getD i ∅ := upward

end PEqualNP.Research.Trace7368

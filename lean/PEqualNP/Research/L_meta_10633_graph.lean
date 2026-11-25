import PEqualNP.Research.L_meta_11718_boundary
import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Research.DenseSeven
open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.SingleInverter

def reference : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [1, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [7, 18]⟩], 19⟩
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def graph (x : Row (Fin 7)) : Bool :=
  ([(0, 3), (1, 3), (0, 4), (2, 4), (0, 5), (1, 5), (3, 5), (4, 5), (1, 6), (2, 6), (3, 6), (4, 6), (5, 6)] : List (Fin 7 × Fin 7)).any
    (fun e => decide (e.1 ∈ x ∧ e.2 ∈ x))

theorem graph_mono : Monotone graph := by
  intro x y h
  simp only [graph,Bool.le_iff_imp,List.any_eq_true,decide_eq_true_eq]
  rintro ⟨e,he,ha,hb⟩
  exact ⟨e,he,h ha,h hb⟩

def rowOf (x : Fin 7 → Bool) : Row (Fin 7) := Finset.univ.filter (fun i => x i)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem graph_posted : ∀ x, graph (rowOf x) = target x := by decide +kernel

theorem reference_size : reference.gates.length = 13 := rfl

theorem reference_legal : ∀ g ∈ reference.gates,
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [reference,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem reference_correct : ∀ x, reference.eval (List.ofFn x) = target x := by decide +kernel

def candidate (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
  (∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j) ∧
  ∀ x, C.eval (List.ofFn x) = target x

def replacement (C : Circuit) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
  gs.length ≤ C.gates.length ∧ ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = target x

theorem small_counterexample : (¬ (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true))) ↔
    ∃ C : Circuit, candidate C ∧ C.gates.length ≤ 12 ∧ ¬ replacement C := by
  classical
  constructor
  · intro h
    by_contra none
    apply h
    intro gs o ok single fits
    by_cases hlarge : 13 ≤ gs.length
    · exact ⟨reference.gates,reference.output,reference_legal,reference_size ▸ hlarge,reference_correct⟩
    · by_contra bad
      exact none ⟨⟨gs,o⟩,⟨ok,single,fits⟩,by change gs.length ≤ 12; omega,bad⟩
  · rintro ⟨C,⟨ok,single,fits⟩,_,bad⟩ h
    exact bad (h C.gates C.output ok single fits)


end PEqualNP.Research.DenseSeven

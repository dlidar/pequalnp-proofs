import PEqualNP.Research.L_meta_11718_graph
import PEqualNP.Research.L_meta_11718_circuits

namespace PEqualNP.Research.InverterRepair
open PEqualNP.CircuitLowerBounds PEqualNP.Research.SingleInverter
open PEqualNP.Research.SevenVertexInverter PEqualNP.Research.InverterCircuit

def stepValue (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map (fun i => w.getD i false))
def substitute (p t : List Gate) (g : Gate) (o : ℕ) := Circuit.mk (p ++ g :: t) o
def withBit (t : List Gate) (o : ℕ) (w : List Bool) (b : Bool) :=
  (run t (w ++ [b])).getD o false

theorem substitution_eval (p t : List Gate) (g : Gate) (o : ℕ) (w : List Bool) :
    (substitute p t g o).eval w = withBit t o (run p w) (stepValue g (run p w)) := by
  simp [substitute,withBit,run,Circuit.eval,Circuit.wires,List.foldl_append,stepValue]

theorem withBit_mono (t : List Gate) (ht : binaryMono t) (o : ℕ) (w : List Bool) :
    Monotone (withBit t o w) := by
  intro a b hab
  exact read_order (run_order ht (List.rel_append (List.forall₂_refl w)
    (List.Forall₂.cons hab List.Forall₂.nil))) o

theorem boundary_repair (pre post : List Gate) (args : List ℕ) (o n : ℕ) (f : Row (Fin n) → Bool)
    (g : Gate) (hp : binaryMono pre) (ht : binaryMono post) (hg : g.op = .and ∨ g.op = .or)
    (fits : ∀ x, out pre post args o x = f x)
    (sep : ∀ x, needed f x = ∅ →
      (if f x then (!signal pre args x) ≤ stepValue g (run pre (input x))
       else stepValue g (run pre (input x)) ≤ (!signal pre args x))) :
    ∀ x, (substitute pre post g o).eval (input x) = f x := by
  let C := substitute pre post g o
  have ok : binaryMono C.gates := by
    intro a ha
    change a ∈ pre ++ g :: post at ha
    rcases List.mem_append.mp ha with h | h
    · exact hp a h
    · rcases List.mem_cons.mp h with rfl | h
      · exact hg
      · exact ht a h
  apply tests_suffice f (fun _ => false) _ ∅ (by intro _ _ _; rfl) ?_ ?_
  · intro x y hxy _
    exact Bool.le_iff_imp.mp (read_order (run_order ok (input_order hxy)) o)
  · intro x hx
    have cmp := sep x (Finset.subset_empty.mp hx)
    have orig := fits x
    change (substitute pre post ⟨.not,args⟩ o).eval (input x) = f x at orig
    rw [substitution_eval] at orig ⊢
    change withBit post o (run pre (input x)) (!signal pre args x) = f x at orig
    cases fx : f x
    · simp only [fx, Bool.false_eq_true, ite_false] at cmp
      exact Bool.eq_false_of_le_false ((withBit_mono post ht o _ cmp).trans (by rw [orig,fx]))
    · simp only [fx, ite_true] at cmp
      exact Bool.eq_true_of_true_le ((by rw [orig,fx] : true ≤ withBit post o (run pre (input x)) (!signal pre args x)).trans (withBit_mono post ht o _ cmp))

def rbit (x : Row (Fin 7)) (i : Fin 7) : Bool := decide (i ∈ x)
def pairSig (join : Bool) (a b : Fin 7) (x : Row (Fin 7)) :=
  if join then rbit x a || rbit x b else rbit x a && rbit x b

def compatible (d r : Row (Fin 7) → Bool) : Bool :=
  decide (∀ x ∈ rows 0, (if graph x then d x || r x else !(d x && r x)) = true)

def oneGate (x : Row (Fin 7)) (d : Bool) (i : Fin 10) :=
  if h : i.val < 7 then rbit x ⟨i.val,h⟩ else if i.val = 7 then d else decide (i.val = 9)

def repairs (d : Row (Fin 7) → Bool) : Bool :=
  [false,true].any (fun join => (List.finRange 10).any (fun i => (List.finRange 10).any (fun j =>
    compatible d (fun x => if join then oneGate x (d x) i || oneGate x (d x) j
      else oneGate x (d x) i && oneGate x (d x) j))))

theorem compatible_iff (d r : Row (Fin 7) → Bool) :
    compatible d r = true ↔ ∀ x, needed graph x = ∅ →
      (if graph x then (!d x) ≤ r x else r x ≤ (!d x)) := by
  simp only [compatible,decide_eq_true_eq]
  constructor
  · intro h x hx
    have hh := h x (by simp [rows,hx] : x ∈ rows 0)
    cases hf : graph x <;> cases hd : d x <;> cases hr : r x <;> simp_all [Bool.le_iff_imp]
  · intro h x hx
    have hh := h x (by simpa [rows] using hx)
    cases hf : graph x <;> cases hd : d x <;> cases hr : r x <;> simp_all [Bool.le_iff_imp]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem raw_classification : ∀ i : Fin 7, repairs (fun x => rbit x i) = false := by decide +kernel

def linked (i j : Fin 7) :=
  ([(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,6),(3,6),(4,5)] : List (Fin 7 × Fin 7)).contains (i,j)
def exceptional (i j : Fin 7) :=
  ([(0,1),(4,6),(5,6)] : List (Fin 7 × Fin 7)).contains (i,j)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem pair_classification : ∀ a b : Fin 7, a < b → ∀ z : Bool,
    repairs (pairSig z a b) = (if z then exceptional a b else linked a b) := by decide +kernel

set_option maxRecDepth 12000 in
theorem explicit_repairs :
    compatible (pairSig true 0 1) (pairSig true 4 6) = true ∧
    compatible (pairSig true 4 6) (pairSig true 0 1) = true ∧
    compatible (pairSig true 5 6) (pairSig true 0 1) = true ∧
    ∀ a b : Fin 7, linked a b = true → compatible (pairSig false a b) (fun _ => true) = true := by
  decide +kernel

end PEqualNP.Research.InverterRepair

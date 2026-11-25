import PEqualNP.Research.PuncturedPlane9838.Substitution
import Mathlib.Data.Finset.NAry

namespace PEqualNP.Research.PuncturedPlane9838
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

abbrev Dnf (n : Nat) := Finset (Finset (Fin n))
def atom (v : Fin n) : Dnf n := {{v}}
def meet (a b : Dnf n) := Finset.image₂ (· ∪ ·) a b
def val (x : Fin n → Bool) (d : Dnf n) : Bool :=
  decide (∃ term ∈ d, ∀ i ∈ term, x i = true)

@[simp] theorem atom_val (x : Fin n → Bool) (i : Fin n) : val x (atom i) = x i := by simp [val,atom]
@[simp] theorem empty_val (x : Fin n → Bool) : val x ∅ = false := by simp [val]
@[simp] theorem unit_val (x : Fin n → Bool) : val x {∅} = true := by simp [val]

@[simp] theorem union_val (x : Fin n → Bool) (a b : Dnf n) :
    val x (a ∪ b) = (val x a || val x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [val,decide_eq_true_eq,Bool.or_eq_true,mem_union]
  aesop

@[simp] theorem meet_val (x : Fin n → Bool) (a b : Dnf n) :
    val x (meet a b) = (val x a && val x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [val,decide_eq_true_eq,Bool.and_eq_true,meet,mem_image₂]
  constructor
  · rintro ⟨_,⟨u,hu,v,hv,rfl⟩,h⟩
    exact ⟨⟨u,hu,fun i hi => h i (mem_union_left _ hi)⟩,⟨v,hv,fun i hi => h i (mem_union_right _ hi)⟩⟩
  · rintro ⟨⟨u,hu,h⟩,⟨v,hv,k⟩⟩
    exact ⟨u ∪ v,⟨u,hu,v,hv,rfl⟩,fun i hi => (mem_union.mp hi).elim (h i) (k i)⟩

def valueAt (w : List (Dnf n)) (i : Nat) : Dnf n := w.getD i ∅
theorem map_value (x : Fin n → Bool) (w : List (Dnf n)) (i : Nat) :
    (w.map (val x)).getD i false = val x (valueAt w i) := by
  unfold valueAt
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem (w.map (val x)) _ (by simpa),List.getD_eq_getElem w _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),List.getD_eq_default _ _ (Nat.le_of_not_gt h),empty_val]

def dgate (w : List (Dnf n)) (g : Gate) :=
  let args := g.inputs.map (valueAt w)
  w ++ [match g.op with
      | .and => args.foldr meet {∅}
      | .or => args.foldr (· ∪ ·) ∅
      | _ => ∅]

theorem dgate_agree (x : Fin n → Bool) (w : List (Dnf n)) (g : Gate) (op : g.op = .and ∨ g.op = .or) :
    (dgate w g).map (val x) = runGate (w.map (val x)) g := by
  have ha (a : List (Dnf n)) : val x (a.foldr meet {∅}) = (a.map (val x)).all id := by
    induction a <;> simp_all
  have hb (a : List (Dnf n)) : val x (a.foldr (· ∪ ·) ∅) = (a.map (val x)).any id := by
    induction a <;> simp_all
  have eq (i : Nat) : (Option.map (val x) w[i]?).getD false = val x (valueAt w i) := by
    simpa [List.getD_eq_getElem?_getD] using map_value x w i
  rcases op with h | h <;> simp [dgate,runGate,h,GateOp.eval,ha,hb,eq,Function.comp_def]

def symbolic (n : Nat) (C : Circuit) : List (Dnf n) := C.gates.foldl dgate (List.ofFn atom)
theorem symbolic_wires (x : Fin n → Bool) (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    (symbolic n C).map (val x) = C.wires (List.ofFn x) := by
  have aux (gs : List Gate) (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w : List (Dnf n)) :
      (gs.foldl dgate w).map (val x) = gs.foldl runGate (w.map (val x)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (fun d hd => h d (List.mem_cons_of_mem _ hd)),dgate_agree x w g (h _ List.mem_cons_self)]
  have start : (List.ofFn (atom : Fin n → Dnf n)).map (val x) = List.ofFn x := by
    apply List.ext_getElem (by simp)
    simp
  unfold symbolic
  rw [aux C.gates mono, start]; rfl

theorem symbolic_lift {n m s : Nat} (P : Circuit) (a : List Nat) (len : a.length = m)
    (hp : FanInTwo P) (mono : ∀ g ∈ P.gates, g.op = .and ∨ g.op = .or)
    (out : P.output < n + P.size) (bd : ∀ i < a.length, a.getD i 0 < n + P.size)
    {f : (Fin m → Bool) → Bool} (d : Dnf n)
    (smallD : (Fin m → Dnf n) → Dnf n)
    (sem : ∀ x q, val x (smallD q) = f (fun i => val x (q i)))
    (certificate : valueAt (symbolic n P) P.output ∪ smallD (fun i => valueAt (symbolic n P) (a.getD i.val 0)) = d)
    (h : HasCircuitSize m f s) : HasCircuitSize n (fun x => val x d) (P.size + s + 1) := by
  apply lift_module P a len hp out bd _ h
  intro x
  have eq := congrArg (val x) certificate
  rw [union_val,sem] at eq
  have port : supplied (m := m) P a x = fun i => val x (valueAt (symbolic n P) (a.getD i.val 0)) := by
    funext i
    unfold supplied
    rw [← symbolic_wires x P mono, map_value]
  rw [port]
  simpa only [Circuit.eval,← symbolic_wires x P mono,map_value] using eq

end PEqualNP.Research.PuncturedPlane9838

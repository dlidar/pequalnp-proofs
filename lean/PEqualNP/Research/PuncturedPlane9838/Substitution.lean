import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Research.PuncturedPlane9838
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runGate (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def remap (a : List Nat) (base w : Nat) :=
  if w < a.length then a.getD w 0 else base + (w - a.length)
def preGate (a : List Nat) (base : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (remap a base)⟩

theorem length_run (w : List Bool) (gs : List Gate) :
    (gs.foldl runGate w).length = w.length + gs.length := by
  induction gs generalizing w <;> simp_all [runGate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem lookup_remap (a : List Nat) (p y v : List Bool) (len : a.length = y.length)
    (bd : ∀ i < a.length, a.getD i 0 < p.length)
    (agree : ∀ i < a.length, p.getD (a.getD i 0) false = y.getD i false) (i : Nat) :
    (p ++ v).getD (remap a p.length i) false = (y ++ v).getD i false := by
  by_cases h : i < a.length
  · simp only [remap,if_pos h]
    rw [List.getD_append _ _ _ _ (bd i h),List.getD_append _ _ _ _ (by omega),agree i h]
  · simp only [remap,if_neg h]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1 <;> omega

theorem fold_remap (a : List Nat) (p y : List Bool) (len : a.length = y.length)
    (bd : ∀ i < a.length, a.getD i 0 < p.length)
    (agree : ∀ i < a.length, p.getD (a.getD i 0) false = y.getD i false)
    (gs : List Gate) (v : List Bool) :
    ∃ w, (gs.map (preGate a p.length)).foldl runGate (p ++ v) = p ++ w ∧
      gs.foldl runGate (y ++ v) = y ++ w := by
  induction gs generalizing v with
  | nil => exact ⟨v,rfl,rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (y ++ v).getD i false)
    have step : runGate (p ++ v) (preGate a p.length g) = p ++ (v ++ [b]) := by
      simp only [b,runGate,preGate,List.map_map,Function.comp_def,lookup_remap a p y v len bd agree,List.append_assoc]
    have old : runGate (y ++ v) g = y ++ (v ++ [b]) := by simp [runGate,b]
    simpa only [List.map_cons,List.foldl_cons,step,old] using ih (v ++ [b])

/-- Compute P, evaluate C with its inputs supplied by the specified wires
of P, then OR the two outputs. The prefix output must be a real wire. -/
def joined (n : Nat) (P : Circuit) (a : List Nat) (C : Circuit) : Circuit :=
  let base := n + P.size
  ⟨P.gates ++ C.gates.map (preGate a base) ++ [⟨.or,[P.output,remap a base C.output]⟩],
    base + C.size⟩

theorem joined_size (n P a C) : (joined n P a C).size = P.size + C.size + 1 := by
  simp [joined,Circuit.size,Nat.add_assoc]

theorem joined_fan (n a) {P C : Circuit} (hp : FanInTwo P) (hc : FanInTwo C) :
    FanInTwo (joined n P a C) := by
  intro g hg
  simp only [joined,List.mem_append,List.mem_map,List.mem_singleton] at hg
  rcases hg with (h | ⟨d,hd,rfl⟩) | rfl
  · exact hp g h
  · simpa [preGate] using hc d hd
  · simp

theorem joined_eval (n : Nat) (P C : Circuit) (a : List Nat) (x : Fin n → Bool)
    (out : P.output < n + P.size) (bd : ∀ i < a.length, a.getD i 0 < n + P.size) :
    let p := P.wires (List.ofFn x)
    (joined n P a C).eval (List.ofFn x) =
      (P.eval (List.ofFn x) || C.eval (a.map fun i => p.getD i false)) := by
  let p := P.wires (List.ofFn x)
  let y := a.map fun i => p.getD i false
  have plen : p.length = n + P.size := by
    change (P.gates.foldl runGate (List.ofFn x)).length = _
    rw [length_run,List.length_ofFn]; rfl
  have yl : a.length = y.length := by simp [y]
  have bdd : ∀ i < a.length, a.getD i 0 < p.length := by simpa [plen] using bd
  have agr : ∀ i < a.length, p.getD (a.getD i 0) false = y.getD i false := by
    intro i hi
    change _ = (a.map _).getD i false
    have hmap : i < (a.map (fun j => p.getD j false)).length := by simpa
    rw [List.getD_eq_getElem (l := a.map (fun j => p.getD j false)) _ hmap,List.getElem_map,
      List.getD_eq_getElem (l := a) _ hi]
  obtain ⟨w,hw,hy⟩ := fold_remap a p y yl bdd agr C.gates []
  simp only [List.append_nil] at hw hy
  let pre := (C.gates.map (preGate a (n+P.size))).foldl runGate p
  have pre_eq : pre = p ++ w := by simpa only [pre,plen] using hw
  have llen : pre.length = n + P.size + C.size := by
    simp [pre,length_run,plen,Circuit.size]
  have lft : pre.getD P.output false = P.eval (List.ofFn x) := by
    rw [pre_eq,List.getD_append _ _ _ _ (by omega)]; rfl
  have rgt : pre.getD (remap a (n+P.size) C.output) false = C.eval y := by
    rw [pre_eq,← plen,lookup_remap a p y w yl bdd agr]; exact congrArg (fun z : List Bool => z.getD C.output false) hy.symm
  change (((P.gates ++ C.gates.map (preGate a (n+P.size)) ++ [_]).foldl runGate (List.ofFn x)).getD _ false) = _
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (pre ++ [_]).getD (n+P.size+C.size) false = _
  rw [← llen,List.getD_append_right _ _ _ _ (by rfl)]
  rw [Nat.sub_self]
  change (pre.getD P.output false || (pre.getD (remap a (n+P.size) C.output) false || false)) = (P.eval (List.ofFn x) || C.eval y)
  rw [Bool.or_false,lft,rgt]

end PEqualNP.Research.PuncturedPlane9838

namespace PEqualNP.Research.PuncturedPlane9838
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def supplied {n m} (P : Circuit) (a : List Nat) (x : Fin n → Bool) (i : Fin m) : Bool :=
  (P.wires (List.ofFn x)).getD (a.getD i.val 0) false

theorem lift_module {n m s : Nat} {f : (Fin m → Bool) → Bool} {target : (Fin n → Bool) → Bool}
    (P : Circuit) (a : List Nat) (len : a.length = m) (hp : FanInTwo P)
    (out : P.output < n + P.size) (bd : ∀ i < a.length, a.getD i 0 < n + P.size)
    (spec : ∀ x, (P.eval (List.ofFn x) || f (supplied P a x)) = target x)
    (hc : HasCircuitSize m f s) : HasCircuitSize n target (P.size + s + 1) := by
  obtain ⟨C,fan,sz,ev⟩ := hc
  refine ⟨joined n P a C,joined_fan n a hp fan,?_,?_⟩
  · rw [joined_size]; omega
  · intro x
    rw [joined_eval n P C a x out bd]
    have lists : (a.map fun i => (P.wires (List.ofFn x)).getD i false) =
        List.ofFn (supplied (m := m) P a x) := by
      apply List.ext_getElem (by simp [len])
      intro i hi hj
      have h : i < a.length := by simpa using hi
      simp only [List.getElem_map,List.getElem_ofFn,supplied,List.getD_eq_getElem _ _ h]
    rw [lists,ev,spec]

end PEqualNP.Research.PuncturedPlane9838

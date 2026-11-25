import PEqualNP.Research.L_meta_10623_channels

namespace PEqualNP.Research.TriangleCosts
open PEqualNP.CircuitLowerBounds PEqualNP.Research.TriangleChannels
abbrev T := BitVec 8

def table (op : GateOp) (l : List T) : T :=
  match op,l with
  | .and, [] => 255
  | .or, [] => 0
  | .and,[a] | .or,[a] => a
  | .and,a::b::_ => a &&& b
  | .or,a::b::_ => a ||| b
  | .not,_ => ~~~(l.headD 0)
  | _,_ => 0

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def legal (gs : List Gate) := ∀ g ∈ gs, allowed g
def raw : List T := [170,204,240]
def initial : List T := 0::255::raw
def run (gs : List Gate) (ws : List T) := gs.foldl
  (fun w g => w ++ [table g.op (g.inputs.map fun i => w.getD i 0)]) ws
def bit (r : Fin 8) (x : T) := x.getLsbD r.val
def read3 (r : Fin 8) (i : Fin 3) := r.val.testBit i.val

theorem raw_reads : ∀ r, raw.map (bit r) = List.ofFn (read3 r) := by decide +kernel

private theorem read_map (r : Fin 8) (w : List T) (i : ℕ) :
    bit r (w.getD i 0) = (w.map (bit r)).getD i false := by
  induction w generalizing i with
  | nil => simp [bit]
  | cons a w ih => cases i with
    | zero => rfl
    | succ k => exact ih k

private theorem gate_correct (r : Fin 8) (op : GateOp) (l : List T)
    (ok : op = .and ∨ op = .or ∨ op = .not) (sz : l.length ≤ 2) :
    bit r (table op l) = op.eval (l.map (bit r)) := by
  have top : bit r 255 = true := by revert r; decide +kernel
  rcases ok with rfl | rfl | rfl <;>
    rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,tail⟩⟩⟩ <;>
    simp_all [table,GateOp.eval,bit,r.isLt]

theorem semantics (gs : List Gate) (w : List T) (h : legal gs) (r : Fin 8) :
    (run gs w).map (bit r) = (Circuit.mk gs 0).wires (w.map (bit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [show run (g::gs) w = run gs (w ++ [table g.op (g.inputs.map fun i => w.getD i 0)]) from rfl]
    rw [ih _ (fun a ha => h a (List.mem_cons_of_mem g ha)),List.map_append,List.map_singleton]
    change (Circuit.mk gs 0).wires _ = (Circuit.mk gs 0).wires (_ ++ [_])
    congr 2
    have op := (h g List.mem_cons_self).1
    have sz := (h g List.mem_cons_self).2
    rw [gate_correct _ _ _ op (by simpa using sz)]
    simp only [List.map_map, Function.comp_def, read_map]

theorem output_table (gs : List Gate) (h : legal gs) (o : ℕ) (r : Fin 8) :
    bit r ((run gs raw).getD o 0) = (Circuit.mk gs o).eval (List.ofFn (read3 r)) := by
  rw [read_map,semantics gs raw h,raw_reads]
  rfl

def choices (w : List T) : List T :=
  (w.map (fun a => ~~~a)) ++ w.flatMap (fun a => w.flatMap (fun b => [a &&& b,a ||| b]))

private theorem gate_choice (op : GateOp) (l w : List T)
    (opok : op = .and ∨ op = .or ∨ op = .not) (sz : l.length ≤ 2)
    (z : 0 ∈ w) (t : 255 ∈ w) (hs : ∀ a ∈ l, a ∈ w) :
    table op l ∈ w ∨ table op l ∈ choices w := by
  have neg (a : T) (ha : a ∈ w) : ~~~a ∈ choices w := by
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have both (a b : T) (ha : a ∈ w) (hb : b ∈ w) :
      (a &&& b) ∈ choices w ∧ (a ||| b) ∈ choices w := by
    constructor <;> apply List.mem_append_right <;> apply List.mem_flatMap.mpr <;>
      refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩ <;> simp
  rcases opok with rfl | rfl | rfl <;>
    rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,tail⟩⟩⟩ <;>
    simp_all [table]

def check (P : List T → Bool) : ℕ → List T → Bool
  | 0,w => P w
  | k+1,w => P w && ((choices w).eraseDups.filter (fun v => !(w.contains v))).all
      (fun v => check P k (v::w))

theorem coverage (P : List T → Bool) (gs : List Gate) (h : legal gs) (w known : List T) (n : ℕ)
    (size : gs.length ≤ n) (z : 0 ∈ known) (t : 255 ∈ known)
    (prev : ∀ i, w.getD i 0 ∈ known) (pass : check P n known = true) :
    ∃ final : List T, P final = true ∧ ∀ i, (run gs w).getD i 0 ∈ final := by
  induction gs generalizing w known n with
  | nil =>
    exact ⟨known,by cases n with
                    | zero => exact pass
                    | succ n => exact (Bool.and_eq_true_iff.mp pass).1,prev⟩
  | cons g gs ih =>
    cases n with
    | zero => simp at size
    | succ n =>
      have hh := h g List.mem_cons_self
      have tailOK : legal gs := fun a ha => h a (List.mem_cons_of_mem g ha)
      let v := table g.op (g.inputs.map fun i => w.getD i 0)
      have vc : v ∈ known ∨ v ∈ choices known := gate_choice _ _ _ hh.1 (by simpa using hh.2)
        z t (by simpa using fun i (_ : i ∈ g.inputs) => prev i)
      have ext (W : List T) (sub : ∀ a ∈ known, a ∈ W) (mem : v ∈ W) :
          ∀ i, (w++[v]).getD i 0 ∈ W := by
        intro i
        by_cases hi : i < w.length
        · rw [List.getD_append _ _ _ _ hi]; exact sub _ (prev i)
        · rw [List.getD_append_right _ _ _ _ (by omega)]
          cases i - w.length with
          | zero => exact mem
          | succ k => exact sub _ z
      by_cases old : v ∈ known
      · exact ih tailOK (w++[v]) known (n+1) (by simp at size; omega) z t (ext _ (fun _ a => a) old) pass
      · have child : check P n (v :: known) = true := by
          apply List.all_eq_true.mp (Bool.and_eq_true_iff.mp pass).2
          simp [vc.resolve_left old,old]
        exact ih tailOK (w++[v]) (v::known) n (by simpa using size)
          (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ t) (ext _ (fun _ => List.mem_cons_of_mem _) List.mem_cons_self) child

def pairOK (u v : T) : Bool := decide (∀ i j : Fin 8,
  (bit i u,bit i v) = (bit j u,bit j v) → profile (read3 i) = profile (read3 j))
def noneDecodes (w : List T) := w.all (fun u => w.all (fun v => !pairOK u v))
def lacksThermometer (w : List T) := !(w.contains 232 && w.contains 254)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem checked_two : check noneDecodes 2 initial = true := by decide +kernel


def next (w : List T) := (choices w).eraseDups.filter (fun v => !(w.contains v))
def lastTest (w : List T) : Bool :=
  if w.contains 232 then !(w.contains 254) && !((choices w).contains 254)
  else if w.contains 254 then !((choices w).contains 232) else true

private theorem last_correct (w : List T) :
    lastTest w = true → check lacksThermometer 1 w = true := by
  intro pass
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  constructor
  · by_cases a : (232 : T) ∈ w <;> by_cases b : (254 : T) ∈ w <;>
      simp_all [lastTest,lacksThermometer]
  · intro v hv
    have vc : v ∈ choices w := by
      exact List.mem_eraseDups.mp (List.mem_filter.mp hv).1
    by_cases a : (232 : T) ∈ w <;> by_cases b : (254 : T) ∈ w <;>
      by_cases c : (232 : T) = v <;> by_cases d : (254 : T) = v <;>
      simp_all [lastTest,lacksThermometer] <;> grind

def walk : ℕ → List T → Bool
  | 0,w => lastTest w
  | n+1,w => lacksThermometer w && (next w).all (fun a => walk n (a::w))

private theorem walk_ok (n : ℕ) (w : List T) (h : walk n w = true) :
    check lacksThermometer (n+1) w = true := by
  induction n generalizing w with
  | zero => exact last_correct w h
  | succ n ih =>
    have ⟨hw,hk⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hw,List.all_eq_true.mpr (fun a ha => ih (a::w) (List.all_eq_true.mp hk a ha))⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem checked_four : check lacksThermometer 4 initial = true := by
  apply walk_ok 3
  decide +kernel

end PEqualNP.Research.TriangleCosts

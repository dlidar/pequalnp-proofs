import PEqualNP.Defs
namespace PEqualNP.Research.FlagWitness3803
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
abbrev Poly := List (List (Fin 26))
def truth (x : Fin 26 → Bool) (P : Poly) := P.any fun t => t.all x
def product (P Q : Poly) : Poly := P.flatMap fun t => Q.map fun s => t ++ s
theorem truth_product (x : Fin 26 → Bool) (P Q : Poly) :
    truth x (product P Q) = (truth x P && truth x Q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [truth,product,List.any_eq_true,List.mem_flatMap,List.mem_map,Bool.and_eq_true]
  constructor
  · rintro ⟨_,⟨t,ht,s,hs,rfl⟩,val⟩
    rw [List.all_append,Bool.and_eq_true] at val
    obtain ⟨vt,vs⟩ := val
    exact ⟨⟨t,ht,vt⟩,s,hs,vs⟩
  · rintro ⟨⟨t,ht,vt⟩,s,hs,vs⟩
    exact ⟨_,⟨t,ht,s,hs,rfl⟩,by simp [vt,vs]⟩

def sym (w : List Poly) (g : Gate) : Poly :=
  let a := w.getD (g.inputs.getD 0 0) []
  let b := w.getD (g.inputs.getD 1 0) []
  if g.op = .and then product a b else a ++ b
def legal (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]
private theorem read_map (x : Fin 26 → Bool) (w : List Poly) (i : ℕ) :
    (w.map (truth x)).getD i false = truth x (w.getD i []) := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]; rfl

theorem symbolic_wires (x : Fin 26 → Bool) (gs : List Gate) (ok : ∀ g ∈ gs, legal g) (xs : List Poly) :
      (gs.foldl (fun z g => z ++ [sym z g]) xs).map (truth x) =
        (Circuit.mk gs 0).wires (xs.map (truth x)) := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (fun t ht => ok t (by simp [ht])),List.map_append,List.map_singleton]
      change (Circuit.mk gs 0).wires _ = (Circuit.mk gs 0).wires (_ ++ [_])
      congr 2
      obtain ⟨op,a,b,ab⟩ := ok g List.mem_cons_self
      have r0 : [a,b].getD 0 0 = a := rfl
      have r1 : [a,b].getD 1 0 = b := rfl
      have join (P Q : Poly) : truth x (P++Q) = (truth x P || truth x Q) := List.any_append
      rcases op with op | op <;>
        simp only [sym,ab,op,r0,r1,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
          List.any_cons,List.any_nil,Bool.and_true,Bool.or_false,read_map,ite_true,truth_product,join,
          reduceCtorEq,ite_false,id_eq]

theorem sym_sound (C : Circuit) (h : ∀ g ∈ C.gates, legal g) (w : List Poly) (x : Fin 26 → Bool) :
    C.eval (w.map (truth x)) =
      truth x ((C.gates.foldl (fun z g => z ++ [sym z g]) w).getD C.output []) := by
  change (C.wires (w.map (truth x))).getD C.output false = _
  rw [← show (C.gates.foldl (fun z g => z ++ [sym z g]) w).map (truth x) = C.wires (w.map (truth x)) from symbolic_wires x C.gates h w,read_map]


def flags : List (Fin 13 × Fin 13) :=
  ((List.finRange 13).flatMap fun i => (List.finRange 13).map fun j => (i,j)).filter fun e =>
    [0,1,3,9].contains (e.1-e.2)
def target (x : Fin 26 → Bool) := flags.any fun e =>
  x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)
def poly : Poly := flags.map fun e => [Fin.castAdd 13 e.1,Fin.natAdd 13 e.2]
theorem exact_target (x : Fin 26 → Bool) : truth x poly = target x := by
  simp [truth,poly,target,Function.comp_def]
def symOut (C : Circuit) (xs : List Poly) :=
  (C.gates.foldl (fun z g => z ++ [sym z g]) xs).getD C.output []
theorem perm_truth (x : Fin 26 → Bool) {a b : Poly} (h : a.toFinset = b.toFinset) :
    truth x a = truth x b := by
  apply Bool.eq_iff_iff.mpr
  simp only [truth,List.any_eq_true]
  have hm (t : List (Fin 26)) : t ∈ a ↔ t ∈ b := by
    simpa only [List.mem_toFinset] using Iff.of_eq (congrArg (fun v => t ∈ v) h)
  simp only [hm]
namespace Points
def C : Circuit := ⟨[⟨.or,[26,3]⟩,⟨.or,[27,9]⟩,⟨.and,[28,13]⟩,⟨.or,[1,2]⟩,⟨.or,[30,4]⟩,⟨.or,[31,10]⟩,⟨.and,[32,14]⟩,⟨.or,[2,3]⟩,⟨.or,[34,5]⟩,⟨.or,[35,11]⟩,⟨.and,[36,15]⟩,⟨.or,[3,4]⟩,⟨.or,[38,6]⟩,⟨.or,[39,12]⟩,⟨.and,[40,16]⟩,⟨.or,[0,4]⟩,⟨.or,[42,5]⟩,⟨.or,[43,7]⟩,⟨.and,[44,17]⟩,⟨.or,[1,5]⟩,⟨.or,[46,6]⟩,⟨.or,[47,8]⟩,⟨.and,[48,18]⟩,⟨.or,[2,6]⟩,⟨.or,[50,7]⟩,⟨.or,[51,9]⟩,⟨.and,[52,19]⟩,⟨.or,[3,7]⟩,⟨.or,[54,8]⟩,⟨.or,[55,10]⟩,⟨.and,[56,20]⟩,⟨.or,[4,8]⟩,⟨.or,[58,9]⟩,⟨.or,[59,11]⟩,⟨.and,[60,21]⟩,⟨.or,[5,9]⟩,⟨.or,[62,10]⟩,⟨.or,[63,12]⟩,⟨.and,[64,22]⟩,⟨.or,[0,6]⟩,⟨.or,[66,10]⟩,⟨.or,[67,11]⟩,⟨.and,[68,23]⟩,⟨.or,[1,7]⟩,⟨.or,[70,11]⟩,⟨.or,[71,12]⟩,⟨.and,[72,24]⟩,⟨.or,[0,2]⟩,⟨.or,[74,8]⟩,⟨.or,[75,12]⟩,⟨.and,[76,25]⟩,⟨.or,[29,33]⟩,⟨.or,[78,37]⟩,⟨.or,[79,41]⟩,⟨.or,[80,45]⟩,⟨.or,[81,49]⟩,⟨.or,[82,53]⟩,⟨.or,[83,57]⟩,⟨.or,[84,61]⟩,⟨.or,[85,65]⟩,⟨.or,[86,69]⟩,⟨.or,[87,73]⟩,⟨.or,[88,77]⟩],89⟩
def inputs : List Poly := List.ofFn (fun i : Fin 26 => [[i]]) ++ [[[0],[1]]]
theorem correct_inputs (x : Fin 26 → Bool) : inputs.map (truth x) =
    (List.ofFn x) ++ [x 0 || x 1] := by simp [inputs,truth]
theorem sizes : C.size = 63 := by decide
theorem backward : ∀ i : Fin C.gates.length, ∀ j ∈ C.gates[i].inputs, j < 27+i.val := by decide +kernel
theorem gates_ok : ∀ g ∈ C.gates, legal g := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨ops,arity⟩ := cert g hg
  refine ⟨ops,?_⟩
  match h : g.inputs with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] => simp [h] at arity
  | [_] => simp [h] at arity
  | _::_::_::_ => simp [h] at arity
theorem mono : Monotone2 C := by
  intro g hg
  obtain ⟨hop,a,b,h⟩ := gates_ok g hg
  exact ⟨hop,by simp [h]⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem covers_flags : (symOut C inputs).toFinset = poly.toFinset := by decide +kernel
theorem computes (x : Fin 26 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 1]) = target x := by
  rw [← correct_inputs,sym_sound C gates_ok,← exact_target]
  exact perm_truth x covers_flags
end Points
namespace Lines
def C : Circuit := ⟨[⟨.or,[13,17]⟩,⟨.or,[27,23]⟩,⟨.or,[28,25]⟩,⟨.and,[0,29]⟩,⟨.or,[26,18]⟩,⟨.or,[31,24]⟩,⟨.and,[1,32]⟩,⟨.or,[14,15]⟩,⟨.or,[34,19]⟩,⟨.or,[35,25]⟩,⟨.and,[2,36]⟩,⟨.or,[13,15]⟩,⟨.or,[38,16]⟩,⟨.or,[39,20]⟩,⟨.and,[3,40]⟩,⟨.or,[14,16]⟩,⟨.or,[42,17]⟩,⟨.or,[43,21]⟩,⟨.and,[4,44]⟩,⟨.or,[15,17]⟩,⟨.or,[46,18]⟩,⟨.or,[47,22]⟩,⟨.and,[5,48]⟩,⟨.or,[16,18]⟩,⟨.or,[50,19]⟩,⟨.or,[51,23]⟩,⟨.and,[6,52]⟩,⟨.or,[17,19]⟩,⟨.or,[54,20]⟩,⟨.or,[55,24]⟩,⟨.and,[7,56]⟩,⟨.or,[18,20]⟩,⟨.or,[58,21]⟩,⟨.or,[59,25]⟩,⟨.and,[8,60]⟩,⟨.or,[13,19]⟩,⟨.or,[62,21]⟩,⟨.or,[63,22]⟩,⟨.and,[9,64]⟩,⟨.or,[14,20]⟩,⟨.or,[66,22]⟩,⟨.or,[67,23]⟩,⟨.and,[10,68]⟩,⟨.or,[15,21]⟩,⟨.or,[70,23]⟩,⟨.or,[71,24]⟩,⟨.and,[11,72]⟩,⟨.or,[16,22]⟩,⟨.or,[74,24]⟩,⟨.or,[75,25]⟩,⟨.and,[12,76]⟩,⟨.or,[30,33]⟩,⟨.or,[78,37]⟩,⟨.or,[79,41]⟩,⟨.or,[80,45]⟩,⟨.or,[81,49]⟩,⟨.or,[82,53]⟩,⟨.or,[83,57]⟩,⟨.or,[84,61]⟩,⟨.or,[85,65]⟩,⟨.or,[86,69]⟩,⟨.or,[87,73]⟩,⟨.or,[88,77]⟩],89⟩
def inputs : List Poly := List.ofFn (fun i : Fin 26 => [[i]]) ++ [[[13],[14]]]
theorem correct_inputs (x : Fin 26 → Bool) : inputs.map (truth x) =
    (List.ofFn x) ++ [x 13 || x 14] := by simp [inputs,truth]
theorem sizes : C.size = 63 := by decide
theorem backward : ∀ i : Fin C.gates.length, ∀ j ∈ C.gates[i].inputs, j < 27+i.val := by decide +kernel
theorem gates_ok : ∀ g ∈ C.gates, legal g := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨ops,arity⟩ := cert g hg
  refine ⟨ops,?_⟩
  match h : g.inputs with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] => simp [h] at arity
  | [_] => simp [h] at arity
  | _::_::_::_ => simp [h] at arity
theorem mono : Monotone2 C := by
  intro g hg
  obtain ⟨hop,a,b,h⟩ := gates_ok g hg
  exact ⟨hop,by simp [h]⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem covers_flags : (symOut C inputs).toFinset = poly.toFinset := by decide +kernel
theorem computes (x : Fin 26 → Bool) : C.eval (List.ofFn x ++ [x 13 || x 14]) = target x := by
  rw [← correct_inputs,sym_sound C gates_ok,← exact_target]
  exact perm_truth x covers_flags
end Lines
namespace Ordinary
def C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[27,3]⟩,⟨.or,[28,9]⟩,⟨.and,[29,13]⟩,⟨.or,[1,2]⟩,⟨.or,[31,4]⟩,⟨.or,[32,10]⟩,⟨.and,[33,14]⟩,⟨.or,[2,3]⟩,⟨.or,[35,5]⟩,⟨.or,[36,11]⟩,⟨.and,[37,15]⟩,⟨.or,[3,4]⟩,⟨.or,[39,6]⟩,⟨.or,[40,12]⟩,⟨.and,[41,16]⟩,⟨.or,[0,4]⟩,⟨.or,[43,5]⟩,⟨.or,[44,7]⟩,⟨.and,[45,17]⟩,⟨.or,[1,5]⟩,⟨.or,[47,6]⟩,⟨.or,[48,8]⟩,⟨.and,[49,18]⟩,⟨.or,[2,6]⟩,⟨.or,[51,7]⟩,⟨.or,[52,9]⟩,⟨.and,[53,19]⟩,⟨.or,[3,7]⟩,⟨.or,[55,8]⟩,⟨.or,[56,10]⟩,⟨.and,[57,20]⟩,⟨.or,[4,8]⟩,⟨.or,[59,9]⟩,⟨.or,[60,11]⟩,⟨.and,[61,21]⟩,⟨.or,[5,9]⟩,⟨.or,[63,10]⟩,⟨.or,[64,12]⟩,⟨.and,[65,22]⟩,⟨.or,[0,6]⟩,⟨.or,[67,10]⟩,⟨.or,[68,11]⟩,⟨.and,[69,23]⟩,⟨.or,[1,7]⟩,⟨.or,[71,11]⟩,⟨.or,[72,12]⟩,⟨.and,[73,24]⟩,⟨.or,[0,2]⟩,⟨.or,[75,8]⟩,⟨.or,[76,12]⟩,⟨.and,[77,25]⟩,⟨.or,[30,34]⟩,⟨.or,[79,38]⟩,⟨.or,[80,42]⟩,⟨.or,[81,46]⟩,⟨.or,[82,50]⟩,⟨.or,[83,54]⟩,⟨.or,[84,58]⟩,⟨.or,[85,62]⟩,⟨.or,[86,66]⟩,⟨.or,[87,70]⟩,⟨.or,[88,74]⟩,⟨.or,[89,78]⟩],90⟩
def inputs : List Poly := List.ofFn (fun i : Fin 26 => [[i]]) ++ [[]]
theorem correct_inputs (x : Fin 26 → Bool) : inputs.map (truth x) =
    (List.ofFn x) ++ [false] := by simp [inputs,truth]
theorem sizes : C.size = 64 := by decide
theorem backward : ∀ i : Fin C.gates.length, ∀ j ∈ C.gates[i].inputs, j < 27+i.val := by decide +kernel
theorem gates_ok : ∀ g ∈ C.gates, legal g := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨ops,arity⟩ := cert g hg
  refine ⟨ops,?_⟩
  match h : g.inputs with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] => simp [h] at arity
  | [_] => simp [h] at arity
  | _::_::_::_ => simp [h] at arity
theorem mono : Monotone2 C := by
  intro g hg
  obtain ⟨hop,a,b,h⟩ := gates_ok g hg
  exact ⟨hop,by simp [h]⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem covers_flags : (symOut C inputs).toFinset = poly.toFinset := by decide +kernel
theorem computes (x : Fin 26 → Bool) : C.eval (List.ofFn x ++ [false]) = target x := by
  rw [← correct_inputs,sym_sound C gates_ok,← exact_target]
  exact perm_truth x covers_flags
end Ordinary
end PEqualNP.Research.FlagWitness3803

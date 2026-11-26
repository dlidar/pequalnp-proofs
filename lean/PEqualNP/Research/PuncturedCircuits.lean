import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.NestedCoverCircuit

namespace PEqualNP.Research.PuncturedCircuits
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Symbolic wire values are positive DNFs in the original 42 variables.
abbrev Poly := List (List (Fin 42))
def truth (x : Fin 42 → Bool) (P : Poly) := P.any fun t => t.all x
def product (P Q : Poly) : Poly := P.flatMap fun t => Q.map fun s => t ++ s
theorem truth_product (x : Fin 42 → Bool) (P Q : Poly) :
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
private theorem read_map (x : Fin 42 → Bool) (w : List Poly) (i : ℕ) :
    (w.map (truth x)).getD i false = truth x (w.getD i []) := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]; rfl

theorem symbolic_wires (x : Fin 42 → Bool) (gs : List Gate) (ok : ∀ g ∈ gs, legal g) (xs : List Poly) :
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

theorem sym_sound (C : Circuit) (h : ∀ g ∈ C.gates, legal g) (w : List Poly) (x : Fin 42 → Bool) :
    C.eval (w.map (truth x)) =
      truth x ((C.gates.foldl (fun z g => z ++ [sym z g]) w).getD C.output []) := by
  change (C.wires (w.map (truth x))).getD C.output false = _
  rw [← show (C.gates.foldl (fun z g => z ++ [sym z g]) w).map (truth x) = C.wires (w.map (truth x)) from symbolic_wires x C.gates h w,read_map]

def raw : List Poly := List.ofFn fun i : Fin 42 => [[i]]
theorem inputs_ok (x : Fin 42 → Bool) : raw.map (truth x) = List.ofFn x := by simp [raw,truth]

namespace Reference
def circuit : Circuit := ⟨[⟨.or,[26,28]⟩,
  ⟨.or,[42,38]⟩,
  ⟨.or,[43,41]⟩,
  ⟨.and,[0,44]⟩,
  ⟨.or,[21,22]⟩,
  ⟨.or,[46,27]⟩,
  ⟨.or,[47,29]⟩,
  ⟨.or,[48,39]⟩,
  ⟨.and,[1,49]⟩,
  ⟨.or,[22,23]⟩,
  ⟨.or,[51,28]⟩,
  ⟨.or,[52,30]⟩,
  ⟨.or,[53,40]⟩,
  ⟨.and,[2,54]⟩,
  ⟨.or,[23,24]⟩,
  ⟨.or,[56,29]⟩,
  ⟨.or,[57,31]⟩,
  ⟨.or,[58,41]⟩,
  ⟨.and,[3,59]⟩,
  ⟨.or,[21,24]⟩,
  ⟨.or,[61,25]⟩,
  ⟨.or,[62,30]⟩,
  ⟨.or,[63,32]⟩,
  ⟨.and,[4,64]⟩,
  ⟨.or,[22,25]⟩,
  ⟨.or,[66,26]⟩,
  ⟨.or,[67,31]⟩,
  ⟨.or,[68,33]⟩,
  ⟨.and,[5,69]⟩,
  ⟨.or,[23,26]⟩,
  ⟨.or,[71,27]⟩,
  ⟨.or,[72,32]⟩,
  ⟨.or,[73,34]⟩,
  ⟨.and,[6,74]⟩,
  ⟨.or,[24,27]⟩,
  ⟨.or,[76,28]⟩,
  ⟨.or,[77,33]⟩,
  ⟨.or,[78,35]⟩,
  ⟨.and,[7,79]⟩,
  ⟨.or,[25,28]⟩,
  ⟨.or,[81,29]⟩,
  ⟨.or,[82,34]⟩,
  ⟨.or,[83,36]⟩,
  ⟨.and,[8,84]⟩,
  ⟨.or,[26,29]⟩,
  ⟨.or,[86,30]⟩,
  ⟨.or,[87,35]⟩,
  ⟨.or,[88,37]⟩,
  ⟨.and,[9,89]⟩,
  ⟨.or,[27,30]⟩,
  ⟨.or,[91,31]⟩,
  ⟨.or,[92,36]⟩,
  ⟨.or,[93,38]⟩,
  ⟨.and,[10,94]⟩,
  ⟨.or,[28,31]⟩,
  ⟨.or,[96,32]⟩,
  ⟨.or,[97,37]⟩,
  ⟨.or,[98,39]⟩,
  ⟨.and,[11,99]⟩,
  ⟨.or,[29,32]⟩,
  ⟨.or,[101,33]⟩,
  ⟨.or,[102,38]⟩,
  ⟨.or,[103,40]⟩,
  ⟨.and,[12,104]⟩,
  ⟨.or,[30,33]⟩,
  ⟨.or,[106,34]⟩,
  ⟨.or,[107,39]⟩,
  ⟨.or,[108,41]⟩,
  ⟨.and,[13,109]⟩,
  ⟨.or,[21,31]⟩,
  ⟨.or,[111,34]⟩,
  ⟨.or,[112,35]⟩,
  ⟨.or,[113,40]⟩,
  ⟨.and,[14,114]⟩,
  ⟨.or,[22,32]⟩,
  ⟨.or,[116,35]⟩,
  ⟨.or,[117,36]⟩,
  ⟨.or,[118,41]⟩,
  ⟨.and,[15,119]⟩,
  ⟨.or,[21,23]⟩,
  ⟨.or,[121,33]⟩,
  ⟨.or,[122,36]⟩,
  ⟨.or,[123,37]⟩,
  ⟨.and,[16,124]⟩,
  ⟨.or,[22,24]⟩,
  ⟨.or,[126,34]⟩,
  ⟨.or,[127,37]⟩,
  ⟨.or,[128,38]⟩,
  ⟨.and,[17,129]⟩,
  ⟨.or,[23,25]⟩,
  ⟨.or,[131,35]⟩,
  ⟨.or,[132,38]⟩,
  ⟨.or,[133,39]⟩,
  ⟨.and,[18,134]⟩,
  ⟨.or,[24,26]⟩,
  ⟨.or,[136,36]⟩,
  ⟨.or,[137,39]⟩,
  ⟨.or,[138,40]⟩,
  ⟨.and,[19,139]⟩,
  ⟨.or,[25,27]⟩,
  ⟨.or,[141,37]⟩,
  ⟨.or,[142,40]⟩,
  ⟨.or,[143,41]⟩,
  ⟨.and,[20,144]⟩,
  ⟨.or,[45,50]⟩,
  ⟨.or,[146,55]⟩,
  ⟨.or,[147,60]⟩,
  ⟨.or,[148,65]⟩,
  ⟨.or,[149,70]⟩,
  ⟨.or,[150,75]⟩,
  ⟨.or,[151,80]⟩,
  ⟨.or,[152,85]⟩,
  ⟨.or,[153,90]⟩,
  ⟨.or,[154,95]⟩,
  ⟨.or,[155,100]⟩,
  ⟨.or,[156,105]⟩,
  ⟨.or,[157,110]⟩,
  ⟨.or,[158,115]⟩,
  ⟨.or,[159,120]⟩,
  ⟨.or,[160,125]⟩,
  ⟨.or,[161,130]⟩,
  ⟨.or,[162,135]⟩,
  ⟨.or,[163,140]⟩,
  ⟨.or,[164,145]⟩],165⟩
theorem size_eq : circuit.size = 124 := rfl
theorem circuit_legal : ∀ g ∈ circuit.gates, legal g := by
  have : ∀ g ∈ circuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs = [g.inputs.getD 0 0,g.inputs.getD 1 0] := by decide +kernel
  intro g hg
  exact ⟨(this _ hg).1,_,_,(this _ hg).2⟩
theorem circuit_mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨op,a,b,h⟩ := circuit_legal g hg
  exact ⟨op,by simp [h]⟩
def terms : Poly := [[0,26], [0,28], [0,38], [0,41], [1,21], [1,22], [1,27], [1,29], [1,39], [2,22], [2,23], [2,28], [2,30], [2,40], [3,23], [3,24], [3,29], [3,31], [3,41], [4,21], [4,24], [4,25], [4,30], [4,32], [5,22], [5,25], [5,26], [5,31], [5,33], [6,23], [6,26], [6,27], [6,32], [6,34], [7,24], [7,27], [7,28], [7,33], [7,35], [8,25], [8,28], [8,29], [8,34], [8,36], [9,26], [9,29], [9,30], [9,35], [9,37], [10,27], [10,30], [10,31], [10,36], [10,38], [11,28], [11,31], [11,32], [11,37], [11,39], [12,29], [12,32], [12,33], [12,38], [12,40], [13,30], [13,33], [13,34], [13,39], [13,41], [14,21], [14,31], [14,34], [14,35], [14,40], [15,22], [15,32], [15,35], [15,36], [15,41], [16,21], [16,23], [16,33], [16,36], [16,37], [17,22], [17,24], [17,34], [17,37], [17,38], [18,23], [18,25], [18,35], [18,38], [18,39], [19,24], [19,26], [19,36], [19,39], [19,40], [20,25], [20,27], [20,37], [20,40], [20,41]]
theorem terms_eq : (circuit.gates.foldl (fun z g => z ++ [sym z g]) raw).getD circuit.output [] = terms := by decide +kernel
theorem eval_terms (x : Fin 42 → Bool) : circuit.eval (List.ofFn x) = truth x terms := by
  rw [←inputs_ok,sym_sound circuit circuit_legal,terms_eq]
def target (x : Fin 42 → Bool) := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)
theorem correct (x : Fin 42 → Bool) : circuit.eval (List.ofFn x) = target x := by
  rw [eval_terms]
  simp [target,truth,terms,Bool.or_assoc]
end Reference
namespace Approx
def circuit : Circuit := ⟨[⟨.or,[26,28]⟩,
  ⟨.or,[42,38]⟩,
  ⟨.or,[43,41]⟩,
  ⟨.and,[0,44]⟩,
  ⟨.or,[21,27]⟩,
  ⟨.or,[46,29]⟩,
  ⟨.or,[47,39]⟩,
  ⟨.and,[1,48]⟩,
  ⟨.or,[22,23]⟩,
  ⟨.or,[50,28]⟩,
  ⟨.or,[51,30]⟩,
  ⟨.or,[52,40]⟩,
  ⟨.and,[2,53]⟩,
  ⟨.or,[23,24]⟩,
  ⟨.or,[55,29]⟩,
  ⟨.or,[56,31]⟩,
  ⟨.or,[57,41]⟩,
  ⟨.and,[3,58]⟩,
  ⟨.or,[21,24]⟩,
  ⟨.or,[60,25]⟩,
  ⟨.or,[61,30]⟩,
  ⟨.or,[62,32]⟩,
  ⟨.and,[4,63]⟩,
  ⟨.or,[22,25]⟩,
  ⟨.or,[65,26]⟩,
  ⟨.or,[66,31]⟩,
  ⟨.or,[67,33]⟩,
  ⟨.and,[5,68]⟩,
  ⟨.or,[23,26]⟩,
  ⟨.or,[70,27]⟩,
  ⟨.or,[71,32]⟩,
  ⟨.or,[72,34]⟩,
  ⟨.and,[6,73]⟩,
  ⟨.or,[24,27]⟩,
  ⟨.or,[75,28]⟩,
  ⟨.or,[76,33]⟩,
  ⟨.or,[77,35]⟩,
  ⟨.and,[7,78]⟩,
  ⟨.or,[25,28]⟩,
  ⟨.or,[80,29]⟩,
  ⟨.or,[81,34]⟩,
  ⟨.or,[82,36]⟩,
  ⟨.and,[8,83]⟩,
  ⟨.or,[26,29]⟩,
  ⟨.or,[85,30]⟩,
  ⟨.or,[86,35]⟩,
  ⟨.or,[87,37]⟩,
  ⟨.and,[9,88]⟩,
  ⟨.or,[27,30]⟩,
  ⟨.or,[90,31]⟩,
  ⟨.or,[91,36]⟩,
  ⟨.or,[92,38]⟩,
  ⟨.and,[10,93]⟩,
  ⟨.or,[28,31]⟩,
  ⟨.or,[95,32]⟩,
  ⟨.or,[96,37]⟩,
  ⟨.or,[97,39]⟩,
  ⟨.and,[11,98]⟩,
  ⟨.or,[29,32]⟩,
  ⟨.or,[100,33]⟩,
  ⟨.or,[101,38]⟩,
  ⟨.or,[102,40]⟩,
  ⟨.and,[12,103]⟩,
  ⟨.or,[30,33]⟩,
  ⟨.or,[105,34]⟩,
  ⟨.or,[106,39]⟩,
  ⟨.or,[107,41]⟩,
  ⟨.and,[13,108]⟩,
  ⟨.or,[21,31]⟩,
  ⟨.or,[110,34]⟩,
  ⟨.or,[111,35]⟩,
  ⟨.or,[112,40]⟩,
  ⟨.and,[14,113]⟩,
  ⟨.or,[22,32]⟩,
  ⟨.or,[115,35]⟩,
  ⟨.or,[116,36]⟩,
  ⟨.or,[117,41]⟩,
  ⟨.and,[15,118]⟩,
  ⟨.or,[21,23]⟩,
  ⟨.or,[120,33]⟩,
  ⟨.or,[121,36]⟩,
  ⟨.or,[122,37]⟩,
  ⟨.and,[16,123]⟩,
  ⟨.or,[22,24]⟩,
  ⟨.or,[125,34]⟩,
  ⟨.or,[126,37]⟩,
  ⟨.or,[127,38]⟩,
  ⟨.and,[17,128]⟩,
  ⟨.or,[23,25]⟩,
  ⟨.or,[130,35]⟩,
  ⟨.or,[131,38]⟩,
  ⟨.or,[132,39]⟩,
  ⟨.and,[18,133]⟩,
  ⟨.or,[24,26]⟩,
  ⟨.or,[135,36]⟩,
  ⟨.or,[136,39]⟩,
  ⟨.or,[137,40]⟩,
  ⟨.and,[19,138]⟩,
  ⟨.or,[25,27]⟩,
  ⟨.or,[140,37]⟩,
  ⟨.or,[141,40]⟩,
  ⟨.or,[142,41]⟩,
  ⟨.and,[20,143]⟩,
  ⟨.or,[45,49]⟩,
  ⟨.or,[145,54]⟩,
  ⟨.or,[146,59]⟩,
  ⟨.or,[147,64]⟩,
  ⟨.or,[148,69]⟩,
  ⟨.or,[149,74]⟩,
  ⟨.or,[150,79]⟩,
  ⟨.or,[151,84]⟩,
  ⟨.or,[152,89]⟩,
  ⟨.or,[153,94]⟩,
  ⟨.or,[154,99]⟩,
  ⟨.or,[155,104]⟩,
  ⟨.or,[156,109]⟩,
  ⟨.or,[157,114]⟩,
  ⟨.or,[158,119]⟩,
  ⟨.or,[159,124]⟩,
  ⟨.or,[160,129]⟩,
  ⟨.or,[161,134]⟩,
  ⟨.or,[162,139]⟩,
  ⟨.or,[163,144]⟩],164⟩
theorem size_eq : circuit.size = 123 := rfl
theorem circuit_legal : ∀ g ∈ circuit.gates, legal g := by
  have : ∀ g ∈ circuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs = [g.inputs.getD 0 0,g.inputs.getD 1 0] := by decide +kernel
  intro g hg
  exact ⟨(this _ hg).1,_,_,(this _ hg).2⟩
theorem circuit_mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨op,a,b,h⟩ := circuit_legal g hg
  exact ⟨op,by simp [h]⟩
def terms : Poly := [[0,26], [0,28], [0,38], [0,41], [1,21], [1,27], [1,29], [1,39], [2,22], [2,23], [2,28], [2,30], [2,40], [3,23], [3,24], [3,29], [3,31], [3,41], [4,21], [4,24], [4,25], [4,30], [4,32], [5,22], [5,25], [5,26], [5,31], [5,33], [6,23], [6,26], [6,27], [6,32], [6,34], [7,24], [7,27], [7,28], [7,33], [7,35], [8,25], [8,28], [8,29], [8,34], [8,36], [9,26], [9,29], [9,30], [9,35], [9,37], [10,27], [10,30], [10,31], [10,36], [10,38], [11,28], [11,31], [11,32], [11,37], [11,39], [12,29], [12,32], [12,33], [12,38], [12,40], [13,30], [13,33], [13,34], [13,39], [13,41], [14,21], [14,31], [14,34], [14,35], [14,40], [15,22], [15,32], [15,35], [15,36], [15,41], [16,21], [16,23], [16,33], [16,36], [16,37], [17,22], [17,24], [17,34], [17,37], [17,38], [18,23], [18,25], [18,35], [18,38], [18,39], [19,24], [19,26], [19,36], [19,39], [19,40], [20,25], [20,27], [20,37], [20,40], [20,41]]
theorem terms_eq : (circuit.gates.foldl (fun z g => z ++ [sym z g]) raw).getD circuit.output [] = terms := by decide +kernel
theorem eval_terms (x : Fin 42 → Bool) : circuit.eval (List.ofFn x) = truth x terms := by
  rw [←inputs_ok,sym_sound circuit circuit_legal,terms_eq]
def target (x : Fin 42 → Bool) := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)
theorem correct (x : Fin 42 → Bool) : circuit.eval (List.ofFn x) = target x := by
  rw [eval_terms]
  simp [target,truth,terms,Bool.or_assoc]
end Approx
theorem deleted_edge (x : Fin 42 → Bool) : Reference.target x = (Approx.target x || (x 1 && x 22)) := by
  simp only [Reference.target,Approx.target, Bool.or_right_comm _ (x 1 && x 22)]

theorem error_iff (x : Fin 42 → Bool) :
    Approx.circuit.eval (List.ofFn x) ≠ Reference.target x ↔
    x 1 = true ∧ x 22 = true ∧ Approx.target x = false := by
  rw [Approx.correct,deleted_edge]
  cases Approx.target x <;> cases x 1 <;> cases x 22 <;> decide

end PEqualNP.Research.PuncturedCircuits

import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Research.Punctured9811
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
def edges : List (Fin 14 × Fin 14) := [(0, 8),(0, 10),(1, 7),(1, 13),(2, 8),(2, 12),(2, 13),(3, 7),(3, 11),(3, 12),(4, 10),(4, 11),(4, 13),(5, 9),(5, 10),(5, 12),(6, 8),(6, 9),(6, 11)]
abbrev Poly := List (List (Fin 14))
def truth (x : Fin 14 → Bool) (P : Poly) := P.any fun t => t.all x
def product (P Q : Poly) : Poly := P.flatMap fun t => Q.map fun s => t ++ s
theorem truth_product (x : Fin 14 → Bool) (P Q : Poly) :
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
private theorem read_map (x : Fin 14 → Bool) (w : List Poly) (i : ℕ) :
    (w.map (truth x)).getD i false = truth x (w.getD i []) := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]; rfl

theorem symbolic_wires (x : Fin 14 → Bool) (gs : List Gate) (ok : ∀ g ∈ gs, legal g) (xs : List Poly) :
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

theorem sym_sound (C : Circuit) (h : ∀ g ∈ C.gates, legal g) (w : List Poly) (x : Fin 14 → Bool) :
    C.eval (w.map (truth x)) =
      truth x ((C.gates.foldl (fun z g => z ++ [sym z g]) w).getD C.output []) := by
  change (C.wires (w.map (truth x))).getD C.output false = _
  rw [← show (C.gates.foldl (fun z g => z ++ [sym z g]) w).map (truth x) = C.wires (w.map (truth x)) from symbolic_wires x C.gates h w,read_map]


def pins : List Poly := List.ofFn fun i : Fin 14 => [[i]]
def graph (e : List (Fin 14 × Fin 14)) (x : Fin 14 → Bool) := e.any fun t => x t.1 && x t.2
def terms (e : List (Fin 14 × Fin 14)) : Poly := e.map fun t => [t.1,t.2]
theorem truth_terms (e : List (Fin 14 × Fin 14)) (x : Fin 14 → Bool) : truth x (terms e) = graph e x := by
  simp [truth,terms,graph,Function.comp_def]
theorem truth_eq (a b : Poly) (h : a.toFinset = b.toFinset) (x : Fin 14 → Bool) :
    truth x a = truth x b := by
  apply Bool.eq_iff_iff.mpr
  simp only [truth,List.any_eq_true]
  have hm (t : List (Fin 14)) : t ∈ a ↔ t ∈ b := by
    simpa only [List.mem_toFinset] using Iff.of_eq (congrArg (fun v => t ∈ v) h)
  simp only [hm]
namespace full
def E : List (Fin 14 × Fin 14) := [(0, 8),(0, 10),(1, 7),(1, 13),(2, 8),(2, 12),(2, 13),(3, 7),(3, 11),(3, 12),(4, 10),(4, 11),(4, 13),(5, 9),(5, 10),(5, 12),(6, 8),(6, 9),(6, 11)]
def C : Circuit := ⟨[⟨.or,[8,10]⟩,⟨.and,[0,14]⟩,⟨.or,[7,13]⟩,⟨.and,[1,16]⟩,⟨.or,[8,12]⟩,⟨.or,[18,13]⟩,⟨.and,[2,19]⟩,⟨.or,[7,11]⟩,⟨.or,[21,12]⟩,⟨.and,[3,22]⟩,⟨.or,[10,11]⟩,⟨.or,[24,13]⟩,⟨.and,[4,25]⟩,⟨.or,[9,10]⟩,⟨.or,[27,12]⟩,⟨.and,[5,28]⟩,⟨.or,[8,9]⟩,⟨.or,[30,11]⟩,⟨.and,[6,31]⟩,⟨.or,[15,17]⟩,⟨.or,[33,20]⟩,⟨.or,[34,23]⟩,⟨.or,[35,26]⟩,⟨.or,[36,29]⟩,⟨.or,[37,32]⟩],38⟩
theorem size : C.size = 25 := rfl
theorem correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = graph E x := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  have ok : ∀ g ∈ C.gates, legal g := by
    intro g hg
    obtain ⟨ops,ar⟩ := cert g hg
    refine ⟨ops,?_⟩
    rcases ls : g.inputs with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩ <;> simp_all
  have pin : pins.map (truth x) = List.ofFn x := by simp [pins,truth]
  rw [← pin,sym_sound C ok,← truth_terms]
  exact truth_eq _ _ (by decide +kernel) x
theorem fan : FanInTwo C := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨op,h⟩ := cert g hg
  rcases op with h'|h' <;> simp [h',h]
end full
namespace dropA
def E : List (Fin 14 × Fin 14) := [(0, 8),(0, 10),(1, 7),(1, 13),(2, 8),(2, 12),(2, 13),(3, 7),(3, 11),(3, 12),(4, 10),(4, 11),(4, 13),(5, 9),(5, 12),(6, 8),(6, 9),(6, 11)]
def C : Circuit := ⟨[⟨.or,[8,10]⟩,⟨.and,[0,14]⟩,⟨.or,[7,13]⟩,⟨.and,[1,16]⟩,⟨.or,[8,12]⟩,⟨.or,[18,13]⟩,⟨.and,[2,19]⟩,⟨.or,[7,11]⟩,⟨.or,[21,12]⟩,⟨.and,[3,22]⟩,⟨.or,[10,11]⟩,⟨.or,[24,13]⟩,⟨.and,[4,25]⟩,⟨.or,[9,12]⟩,⟨.and,[5,27]⟩,⟨.or,[8,9]⟩,⟨.or,[29,11]⟩,⟨.and,[6,30]⟩,⟨.or,[15,17]⟩,⟨.or,[32,20]⟩,⟨.or,[33,23]⟩,⟨.or,[34,26]⟩,⟨.or,[35,28]⟩,⟨.or,[36,31]⟩],37⟩
theorem size : C.size = 24 := rfl
theorem correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = graph E x := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  have ok : ∀ g ∈ C.gates, legal g := by
    intro g hg
    obtain ⟨ops,ar⟩ := cert g hg
    refine ⟨ops,?_⟩
    rcases ls : g.inputs with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩ <;> simp_all
  have pin : pins.map (truth x) = List.ofFn x := by simp [pins,truth]
  rw [← pin,sym_sound C ok,← truth_terms]
  exact truth_eq _ _ (by decide +kernel) x
theorem fan : FanInTwo C := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨op,h⟩ := cert g hg
  rcases op with h'|h' <;> simp [h',h]
end dropA
namespace dropB
def E : List (Fin 14 × Fin 14) := [(0, 8),(0, 10),(1, 7),(1, 13),(2, 8),(2, 12),(2, 13),(3, 7),(3, 11),(3, 12),(4, 10),(4, 11),(4, 13),(5, 9),(5, 10),(5, 12),(6, 9),(6, 11)]
def C : Circuit := ⟨[⟨.or,[8,10]⟩,⟨.and,[0,14]⟩,⟨.or,[7,13]⟩,⟨.and,[1,16]⟩,⟨.or,[8,12]⟩,⟨.or,[18,13]⟩,⟨.and,[2,19]⟩,⟨.or,[7,11]⟩,⟨.or,[21,12]⟩,⟨.and,[3,22]⟩,⟨.or,[10,11]⟩,⟨.or,[24,13]⟩,⟨.and,[4,25]⟩,⟨.or,[9,10]⟩,⟨.or,[27,12]⟩,⟨.and,[5,28]⟩,⟨.or,[9,11]⟩,⟨.and,[6,30]⟩,⟨.or,[15,17]⟩,⟨.or,[32,20]⟩,⟨.or,[33,23]⟩,⟨.or,[34,26]⟩,⟨.or,[35,29]⟩,⟨.or,[36,31]⟩],37⟩
theorem size : C.size = 24 := rfl
theorem correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = graph E x := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  have ok : ∀ g ∈ C.gates, legal g := by
    intro g hg
    obtain ⟨ops,ar⟩ := cert g hg
    refine ⟨ops,?_⟩
    rcases ls : g.inputs with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩ <;> simp_all
  have pin : pins.map (truth x) = List.ofFn x := by simp [pins,truth]
  rw [← pin,sym_sound C ok,← truth_terms]
  exact truth_eq _ _ (by decide +kernel) x
theorem fan : FanInTwo C := by
  have cert : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by decide +kernel
  intro g hg
  obtain ⟨op,h⟩ := cert g hg
  rcases op with h'|h' <;> simp [h',h]
end dropB

end PEqualNP.Research.Punctured9811

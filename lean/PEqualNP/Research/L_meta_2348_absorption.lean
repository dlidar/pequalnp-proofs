import PEqualNP.Research.L_meta_2348_tangent

namespace PEqualNP.Research.FlagAbsorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Research.FanoTangent
open PEqualNP.ReadK

/-- With a spare old wire, an OR and an AND preserve the output yet can suppress
every linear term at once. Both gates read distinct earlier wires. -/
def extend (n : ℕ) (C : Circuit) (r : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or,[C.output,r]⟩, ⟨.and,[C.output,n+C.size]⟩], n+C.size+1⟩

theorem size (C : Circuit) (n r : ℕ) : (extend n C r).size = C.size + 2 := by
  simp [Circuit.size,extend]

theorem get_end {α : Type} (xs : List α) (v d : α) :
    (xs ++ [v]).getD xs.length d = v := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]

theorem last_two {α : Type} (xs : List α) (u v d : α) :
    ((xs ++ [u]) ++ [v]).getD (xs.length+1) d = v := by
  simpa using get_end (xs ++ [u]) v d

theorem unchanged (n : ℕ) (C : Circuit) (r : ℕ) (h : C.output < n+C.size)
    (x : List Bool) (hx : x.length = n) :
    (extend n C r).eval x = C.eval x := by
  let w := scan boolStep C.gates x
  have len : w.length = n + C.size := by simp [w,scan_length,hx,Circuit.size]
  change (scan boolStep (C.gates ++ _) x).getD (n + C.size + 1) false = w.getD C.output false
  rw [scan_append]
  change (((w ++ [boolStep w ⟨.or,[C.output,r]⟩]) ++
    [boolStep (w ++ [boolStep w ⟨.or,[C.output,r]⟩]) ⟨.and,[C.output,n+C.size]⟩]).getD
    (n+C.size+1) false) = _
  rw [← len,last_two]
  let g := boolStep w ⟨.or,[C.output,r]⟩
  have ho := List.getD_append w [g] false C.output (show C.output < w.length by omega)
  change boolStep (w ++ [g]) ⟨.and,[C.output,w.length]⟩ = _
  simp only [boolStep,List.map_cons,List.map_nil, GateOp.eval,List.all_cons,List.all_nil,
    Bool.and_true,ho,get_end]
  simp [g,boolStep,GateOp.eval]
  exact Or.inl

theorem kills_linear (n : ℕ) (C : Circuit) (r : ℕ) (h : C.output < n+C.size)
    (isLine : ℕ → Bool) (x : List Bool) (hx : x.length = n)
    (hOut : ((linearParts C isLine x).getD C.output (false,false)).1 = false)
    (hAux : ((linearParts C isLine x).getD r (false,false)).1 = false) :
    (linearParts (extend n C r) isLine x).getD (n+C.size+1) (false,false) = (false,false) := by
  let w := linearParts C isLine x
  have len : w.length = n+C.size := by simp [w,linearParts_eq_scan,scan_length,hx,Circuit.size]
  rw [linearParts_eq_scan]
  change (scan linStep (C.gates ++ _) _).getD _ _ = _
  rw [scan_append]
  change (((w ++ [linStep w ⟨.or,[C.output,r]⟩]) ++
    [linStep (w ++ [linStep w ⟨.or,[C.output,r]⟩]) ⟨.and,[C.output,n+C.size]⟩]).getD
    (n+C.size+1) (false,false)) = _
  rw [← len,last_two]
  let g := linStep w ⟨.or,[C.output,r]⟩
  have ho := List.getD_append w [g] (false,false) C.output (show C.output < w.length by omega)
  change linStep (w ++ [g]) ⟨.and,[C.output,w.length]⟩ = _
  change (w.getD C.output (false,false)).1 = false at hOut
  change (w.getD r (false,false)).1 = false at hAux
  have hg : g.1 = false := by
    simp only [g, linStep, List.map_cons,List.map_nil,List.any_cons,List.any_nil,hOut,hAux]
    rfl
  simp only [linStep,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,ho,get_end,
    hOut,hg,Bool.true_and,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
#print axioms unchanged
#print axioms kills_linear
end PEqualNP.Research.FlagAbsorption

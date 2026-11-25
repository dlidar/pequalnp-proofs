import PEqualNP.Research.L_meta_2223_marked_depth

namespace PEqualNP.Research.DepthExamples
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.MarkedAndDepth

/-- Two old wires are followed by their OR and two distinct-operand ANDs. -/
def layer (k : Nat) : List Gate :=
  [⟨.or,[k,k+1]⟩, ⟨.and,[k,k+2]⟩, ⟨.and,[k,k+1]⟩]
def stages : Nat → List Gate
  | 0 => []
  | d+1 => stages d ++ layer (3*d)
def exampleAt (d : Nat) (accepted : Bool) : Circuit :=
  ⟨stages d,3*d + (if accepted then 0 else 1)⟩

theorem size (d : Nat) (a : Bool) : (exampleAt d a).size = 3*d := by
  change (stages d).length = _
  induction d with
  | zero => rfl
  | succ d ih => simp [stages,layer,ih,Nat.mul_succ]

def ops (k : Nat) (g : Gate) := (g.op = .and ∨ g.op = .or) ∧
  ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < k ∧ b < k

theorem legal (d : Nat) : ∀ j g, (stages d)[j]? = some g → ops (2+j) g := by
  induction d with
  | zero => simp [stages]
  | succ d ih =>
    intro j g h
    have len : (stages d).length = 3*d := size d true
    by_cases lt : j < (stages d).length
    · exact ih _ _ (by simpa [stages,List.getElem?_append_left lt] using h)
    · have le : (stages d).length ≤ j := by omega
      rw [stages,List.getElem?_append_right le,len] at h
      generalize eq : j-3*d = i at h
      rcases i with _ | _ | _ | i
      all_goals simp [layer,List.getElem?_cons_succ] at h
      all_goals subst g; simp [ops]; omega

/-- The last two wires of a fold, with the prefix length retained. -/
def Ends {α : Type} (k : Nat) (x y : α) (w : List α) :=
  ∃ pre, pre.length = k ∧ w = pre ++ [x,y]

private theorem liftLayer {α : Type} (step : List α → Gate → List α) (join meet : α → α → α)
    (z : α) (binary : ∀ w i j, step w ⟨.or,[i,j]⟩ = w ++ [join (w.getD i z) (w.getD j z)] ∧
      step w ⟨.and,[i,j]⟩ = w ++ [meet (w.getD i z) (w.getD j z)])
    {w k x y} (h : Ends k x y w) : Ends (k+3) (meet x (join x y)) (meet x y)
      ((layer k).foldl step w) := by
  obtain ⟨p,rfl,rfl⟩ := h
  let u := join x y
  refine ⟨p ++ [x,y,u],by simp,?_⟩
  simp only [layer,List.foldl_cons,List.foldl_nil,(binary ..).1,(binary ..).2,List.append_assoc]
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right,u]

private theorem reads (d : Nat) : Ends (3*d) (2^d) (2^d-1) ((stages d).foldl degreeStep [1,0]) := by
  induction d with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ d ih =>
    have pos : 0 < 2^d := by positivity
    have h := liftLayer degreeStep max Nat.add 0 (by intros; simp [degreeStep,Gate.lineDegree]) ih
    rw [max_eq_left (by omega : 2^d-1 ≤ 2^d)] at h
    change Ends _ (2^d+2^d) (2^d+(2^d-1)) _ at h
    rw [show 2^d + 2^d = 2^(d+1) by rw [pow_succ]; omega,
      show 2^d+(2^d-1)=2^(d+1)-1 by rw [pow_succ]; omega] at h
    simpa only [stages,Nat.mul_succ,List.foldl_append] using h

private theorem depths (d : Nat) : Ends (3*d) d d ((stages d).foldl depthStep [0,0]) := by
  induction d with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ d ih =>
    simpa [stages,Nat.mul_succ,List.foldl_append] using
      liftLayer depthStep max (fun x y => max x y+1) 0
        (by intros; simp [depthStep,SingleLevel.andLevel]) ih

private theorem vals (d : Nat) : Ends (3*d) true false ((stages d).foldl boolStep [true,false]) := by
  induction d with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ d ih =>
    simpa [stages,Nat.mul_succ,List.foldl_append] using
      liftLayer boolStep Bool.or Bool.and false (by intros; simp [boolStep,GateOp.eval]) ih

private theorem output {α : Type} {x y : α} {w : List α} {d : Nat} (z : α) (a : Bool)
    (h : Ends (3*d) x y w) : w.getD (exampleAt d a).output z = (if a then x else y) := by
  obtain ⟨p,hl,rfl⟩ := h
  cases a <;> simp [exampleAt,← hl,List.getD_eq_getElem?_getD,List.getElem?_append_right]

theorem sharp (d : Nat) (a : Bool) :
    (exampleAt d a).lineDeg 2 {0} = (if a then 2^d else 2^d-1) ∧
    ((SingleLevel.andDepths (exampleAt d a) 2).getD (exampleAt d a).output 0) = d ∧
    (exampleAt d a).eval [true,false] = a := by
  refine ⟨output 0 a (reads d),?_,?_⟩
  · change ((stages d).foldl depthStep [0,0]).getD (exampleAt d a).output 0 = d
    simpa using output 0 a (depths d)
  · cases a <;> exact output false _ (vals d)
end PEqualNP.Research.DepthExamples

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.MarkedAndDepth
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- At equality, a maximal parse can use only marked inputs. -/
def Bound (v d : Nat) (b : Bool) := v ≤ 2^d ∧ (v = 2^d → b = true)

theorem and_bound {p q u v : Nat} {a b : Bool} (h : Bound p u a) (k : Bound q v b) :
    Bound (p+q) (max u v + 1) (a && b) := by
  have hu : 2^u ≤ (2:Nat)^(max u v) := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hv : 2^v ≤ (2:Nat)^(max u v) := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  obtain ⟨hp,ha⟩ := h
  obtain ⟨hq,hb⟩ := k
  unfold Bound
  rw [pow_succ]
  constructor
  · omega
  · intro eq
    rw [ha (by omega),hb (by omega)]; rfl

theorem or_bound {p q u v : Nat} {a b : Bool} (h : Bound p u a) (k : Bound q v b) :
    Bound (max p q) (max u v) (a || b) := by
  have hu : 2^u ≤ (2:Nat)^(max u v) := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hv : 2^v ≤ (2:Nat)^(max u v) := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  obtain ⟨hp,ha⟩ := h
  obtain ⟨hq,hb⟩ := k
  constructor
  · omega
  · intro eq
    by_cases hh : p ≥ q
    · simp [ha (by omega)]
    · simp [hb (by omega)]

def Reads (v d : List Nat) (b : List Bool) := ∀ i, Bound (v.getD i 0) (d.getD i 0) (b.getD i false)

theorem append {v d : List Nat} {b : List Bool} {p h : Nat} {a : Bool}
    (len : d.length = v.length) (len' : b.length = v.length) (old : Reads v d b) (new : Bound p h a) :
    Reads (v++[p]) (d++[h]) (b++[a]) := by
  intro i
  by_cases hi : i < v.length
  · simpa only [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi : i < d.length),
      List.getD_append _ _ _ _ (len' ▸ hi : i < b.length)] using old i
  · simp only [List.getD_append_right _ _ _ _ (by omega : v.length ≤ i),
      List.getD_append_right _ _ _ _ (by omega : d.length ≤ i),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ i),len,len']
    cases i-v.length with
    | zero => exact new
    | succ k => simp [Bound,List.getD]

def degreeStep (v : List Nat) (g : Gate) := v ++ [g.lineDegree v]
def depthStep (d : List Nat) (g : Gate) := d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + SingleLevel.andLevel g]
def boolStep (b : List Bool) (g : Gate) := b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]

theorem fold_bound (gs : List Gate) (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    {v d : List Nat} {b : List Bool} (len : d.length = v.length) (len' : b.length = v.length)
    (old : Reads v d b) :
    Reads (gs.foldl degreeStep v) (gs.foldl depthStep d) (gs.foldl boolStep b) := by
  induction gs generalizing v d b with
  | nil => exact old
  | cons g gs ih =>
    apply ih (fun a ha => legal a (by simp [ha])) (by simp [depthStep,degreeStep,len])
      (by simp [boolStep,degreeStep,len'])
    apply append len len' old
    obtain ⟨op,arity⟩ := legal g (by simp)
    obtain ⟨i,j,eq⟩ : ∃ i j, g.inputs = [i,j] := by
      cases args : g.inputs with
      | nil => simp [args] at arity
      | cons i l =>
        cases l with
        | nil => simp [args] at arity
        | cons j l =>
          have hl : l = [] := by simpa [args] using arity
          exact ⟨i,j,by rw [hl]⟩
    rcases g with ⟨o,ins⟩
    change ins = [i,j] at eq
    subst ins
    rcases op with rfl | rfl
    · simpa [Gate.lineDegree,GateOp.eval,SingleLevel.andLevel] using and_bound (old i) (old j)
    · simpa [Gate.lineDegree,GateOp.eval,SingleLevel.andLevel] using or_bound (old i) (old j)

def marked (n : Nat) (S : Finset Nat) : List Bool := (List.range n).map (fun i => decide (i ∈ S))

theorem output_bound (n : Nat) (C : Circuit) (S : Finset Nat)
    (ok : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    Bound (C.lineDeg n S) ((SingleLevel.andDepths C n).getD C.output 0) (C.eval (marked n S)) := by
  let v := (List.range n).map (fun i => if i ∈ S then 1 else 0)
  apply fold_bound C.gates ok (v := v) (d := List.replicate n 0) (b := marked n S)
      (by simp [v]) (by simp [v,marked]) _ C.output
  intro i
  by_cases hi : i < n
  · simp [v,marked,List.getD_eq_getElem,hi,Bound]
    split <;> simp_all
  · simp [v,marked,Bound,List.getD_eq_default,hi,Nat.le_of_not_gt hi]

theorem depthOfRepeatedLabel (n : Nat) (C : Circuit) (i : Fin n) (ok : PEqualNP.TopForm.IsAO2 n C)
    (off : C.eval (List.ofFn (fun j : Fin n => decide (j=i))) = false)
    (twice : 2 ≤ C.lineDeg n {i.val}) : 2 ≤ (SingleLevel.andDepths C n).getD C.output 0 := by
  have bits : marked n {i.val} = List.ofFn (fun j : Fin n => decide (j=i)) := by
    apply List.ext_getElem <;> simp [marked,Fin.ext_iff]
  obtain ⟨bound,tight⟩ := output_bound n C {i.val} (fun g hg => ⟨ok.1 g hg,ok.2.2 g hg⟩)
  rw [bits,off] at tight
  by_contra h
  have cases' : (SingleLevel.andDepths C n).getD C.output 0 = 0 ∨ (SingleLevel.andDepths C n).getD C.output 0 = 1 := by omega
  rcases cases' with hh | hh <;> rw [hh] at bound tight <;> norm_num at bound tight <;> omega

end PEqualNP.Research.MarkedAndDepth

import PEqualNP.Research.L_meta_2223_marked_depth

namespace PEqualNP.Research.LongestParse
open PEqualNP.CircuitLowerBounds PEqualNP.Research.MarkedAndDepth
/-- Keep precisely the children of an OR that can attain its largest parse. -/
def filterGate (cap : List Nat) (g : Gate) : Gate :=
  match g.op,g.inputs with
  | .or,[a,b] =>
    if cap.getD a 0 < cap.getD b 0 then ⟨.or,[b]⟩
    else if cap.getD b 0 < cap.getD a 0 then ⟨.or,[a]⟩ else g
  | _,_ => g

def select : List Gate → List Nat → List Gate
  | [],_ => []
  | g::gs,c => filterGate c g :: select gs (degreeStep c g)

def Well (k : Nat) (gs : List Gate) := ∀ j g, gs[j]? = some g →
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a < k+j ∧ b < k+j

theorem count (gs : List Gate) (cap : List Nat) : (select gs cap).length = gs.length := by
  induction gs generalizing cap <;> simp [select, *]

def Rel (v cap : List Nat) (xs ys : List Bool) := ∀ i < cap.length,
  v.getD i 0 ≤ cap.getD i 0 ∧
  (ys.getD i false = true ↔ v.getD i 0 = cap.getD i 0) ∧
  (ys.getD i false = true → xs.getD i false = true)

private theorem push {v cap xs ys a b p q}
    (lv : v.length = cap.length) (lx : xs.length = cap.length) (ly : ys.length = cap.length)
    (h : Rel v cap xs ys) (bound : a ≤ b) (yes : q = true ↔ a = b) (refines : q = true → p = true) :
    Rel (v++[a]) (cap++[b]) (xs++[p]) (ys++[q]) := by
  intro i hi
  by_cases lt : i < cap.length
  · simpa only [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (lv ▸ lt : i < v.length),
      List.getD_append _ _ _ _ (lx ▸ lt : i < xs.length),List.getD_append _ _ _ _ (ly ▸ lt : i < ys.length)] using h i lt
  · have eq : i = cap.length := by simp at hi; omega
    subst i
    simp only [List.getD_append_right _ _ _ _ (by omega : v.length ≤ cap.length),
      List.getD_append_right _ _ _ _ (by omega : xs.length ≤ cap.length),
      List.getD_append_right _ _ _ _ (by omega : ys.length ≤ cap.length),
      List.getD_append_right _ _ _ _ (le_refl _),lv,lx,ly,Nat.sub_self,List.getD_cons_zero]
    exact ⟨bound,yes,refines⟩

attribute [-simp] List.getD_eq_getElem?_getD in
theorem track (gs : List Gate) {v cap xs ys} (wf : Well cap.length gs)
    (lv : v.length = cap.length) (lx : xs.length = cap.length) (ly : ys.length = cap.length)
    (h : Rel v cap xs ys) : Rel (gs.foldl degreeStep v) (gs.foldl degreeStep cap)
      (gs.foldl boolStep xs) ((select gs cap).foldl boolStep ys) := by
  induction gs generalizing v cap xs ys with
  | nil => exact h
  | cons g gs ih =>
    apply ih (v := degreeStep v g) (cap := degreeStep cap g) (xs := boolStep xs g)
      (ys := boolStep ys (filterGate cap g))
    · intro j z hz
      simpa [degreeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using wf (j+1) z (by simpa using hz)
    · simp [degreeStep,lv]
    · simp [degreeStep,boolStep,lx]
    · simp [degreeStep,boolStep,ly]
    obtain ⟨ops,a,b,args,aa,bb⟩ := wf 0 g (by simp)
    obtain ⟨ha,ea,sa⟩ := h a (by simpa using aa)
    obtain ⟨hb,eb,sb⟩ := h b (by simpa using bb)
    rcases g with ⟨op,ins⟩
    change ins = [a,b] at args
    subst ins
    rcases ops with rfl | rfl
    · apply push lv lx ly h
      · simpa [Gate.lineDegree] using Nat.add_le_add ha hb
      · simp [filterGate, GateOp.eval,Gate.lineDegree,ea,eb]
        omega
      · simp [filterGate,GateOp.eval]
        tauto
    · rcases lt_trichotomy (cap.getD a 0) (cap.getD b 0) with hab | hab | hab
      · apply push lv lx ly h
        · simpa [Gate.lineDegree] using max_le_max ha hb
        · simp [filterGate,Gate.lineDegree,GateOp.eval,hab,eb]
          omega
        · simp [filterGate,GateOp.eval,hab]
          tauto
      · apply push lv lx ly h
        · simpa [Gate.lineDegree] using max_le_max ha hb
        · simp [filterGate,Gate.lineDegree,GateOp.eval,hab,ea,eb]
          omega
        · simp [filterGate,GateOp.eval,hab]
          tauto
      · have no := Nat.not_lt.mpr (Nat.le_of_lt hab)
        apply push lv lx ly h
        · simpa [Gate.lineDegree] using max_le_max ha hb
        · simp [filterGate,Gate.lineDegree,GateOp.eval,hab,no,ea]
          omega
        · simp [filterGate,GateOp.eval,hab,no]
          tauto

def longest (n : Nat) (C : Circuit) : Circuit := ⟨select C.gates (List.replicate n 1), C.output⟩

theorem longest_size (C : Circuit) (n : Nat) : (longest n C).size = C.size := count _ _

theorem at_output (n : Nat) (C : Circuit) (S : Finset Nat) (wf : Well n C.gates)
    (live : C.output < n + C.size) :
    ((longest n C).eval (marked n S) = true ↔ C.lineDeg n S = C.lineDeg n (Finset.range n)) ∧
      ((longest n C).eval (marked n S) = true → C.eval (marked n S) = true) := by
  let v := (List.range n).map (fun i => if i ∈ S then 1 else 0)
  let cap := List.replicate n 1
  have init : Rel v cap (marked n S) (marked n S) := by
    intro i hi
    have lt : i < n := by simpa [cap] using hi
    by_cases ii : i ∈ S <;> simp [v,cap,marked,lt,ii]
  have length (gs : List Gate) (c : List Nat) : (gs.foldl degreeStep c).length = c.length + gs.length := by
    induction gs generalizing c with
    | nil => simp
    | cons g gs ih => simp [List.foldl_cons,ih,degreeStep,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  have capEq : (List.range n).map (fun i => if i ∈ Finset.range n then 1 else 0) = cap := by
    apply List.ext_getElem <;> simp [cap]
  have all := track C.gates (v := v) (cap := cap) (xs := marked n S) (ys := marked n S)
    (by simpa [cap] using wf) (by simp [cap,v]) (by simp [cap,marked]) (by simp [cap,marked]) init
    C.output (by simpa [length,cap,Circuit.size] using live)
  unfold Circuit.lineDeg Circuit.lineDegrees
  rw [capEq]
  exact all.2

theorem strict_of_rejected (n : Nat) (C : Circuit) (S : Finset Nat) (wf : Well n C.gates)
    (live : C.output < n+C.size) (off : C.eval (marked n S) = false) :
    C.lineDeg n S ≠ C.lineDeg n (Finset.range n) := by
  intro eq
  obtain ⟨iff',le⟩ := at_output n C S wf live
  simpa [off] using le (iff'.2 eq)
end PEqualNP.Research.LongestParse

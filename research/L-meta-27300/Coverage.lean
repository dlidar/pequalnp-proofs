import Wires
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
def uses (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs
theorem insensitivity {m : ℕ} (C : Circuit) (ha : ReadsBack m C) (u : Fin m)
    (hu : u.val ∉ uses C) (x y : Fin m → Bool) (hxy : ∀ v ≠ u, x v = y v) :
    circuitFun m C x = circuitFun m C y := by
  have hw : ∀ a : ℕ, a ≠ u.val →
      (C.wires (List.ofFn x)).getD a false = (C.wires (List.ofFn y)).getD a false := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro hne
      by_cases h : a < m
      · rw [wires_low _ _ _ (by simpa using h), wires_low _ _ _ (by simpa using h)]
        simpa [List.getD_eq_getElem, h] using hxy ⟨a,h⟩ (fun h => hne (congrArg Fin.val h))
      by_cases hp : m + C.gates.length ≤ a
      · rw [wires_past _ _ _ (by simpa using hp),wires_past _ _ _ (by simpa using hp)]
      let j := a-m
      have hj : j < C.gates.length := by dsimp [j]; omega
      have eq : a = m+j := by dsimp [j]; omega
      rw [eq,wires_gate _ _ _ (List.length_ofFn ..) ha j hj,wires_gate _ _ _ (List.length_ofFn ..) ha j hj]
      congr 1
      apply List.map_congr_left
      intro b hb
      have back := ha j hj b
      rw [gateAt,List.getD_eq_getElem _ _ hj] at back
      apply ih b (eq ▸ back hb)
      intro e
      apply hu
      exact e ▸ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem .., hb⟩)
  exact hw _ (fun h => hu (by simp [uses,h]))


def first : Gate := ⟨.and,[0,1]⟩
def second : Gate := ⟨.and,[5,8]⟩
def px (s : Fin 512) (i : Fin 9) := s.val.testBit i.val
def perm3 (x : Fin 9 → Bool) := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
def extended (s : Fin 512) (i : Fin 11) : Bool :=
  if i.val = 9 then px s 0 && px s 1 else if i.val = 10 then px s 5 && px s 8 else s.val.testBit i.val
def pref (x : List Bool) := ([first,second] : List Gate).foldl (fun w g => w ++ [readGate w g]) x
theorem initial_rows : ∀ s : Fin 512, List.ofFn (extended s) = pref (List.ofFn (px s)) := by decide +kernel
def flip (i : Fin 9) : Fin 512 × Fin 512 := ([(160, 161), (96, 98), (80, 84), (132, 140), (68, 84), (66, 98), (20, 84), (12, 140), (10, 266)] : List (Fin 512 × Fin 512)).getD i.val (0,0)

theorem flips : ∀ i : Fin 9,
    (∀ j : Fin 11, j.val ≠ i.val → extended (flip i).1 j = extended (flip i).2 j) ∧
    perm3 (px (flip i).1) ≠ perm3 (px (flip i).2) := by decide +kernel

theorem early_eval (gs : List Gate) (o : ℕ) (s : Fin 512) :
    (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (px s)) =
    (Circuit.mk gs o).eval (List.ofFn (extended s)) := by
  rw [initial_rows]
  rfl

theorem raw_coverage {gs : List Gate} {o : ℕ}
    (hb : ReadsBack 11 ⟨gs,o⟩)
    (he : ∀ x, (Circuit.mk (first :: second :: gs) o).eval (List.ofFn x) = perm3 x) :
    ∀ i : Fin 9, i.val ∈ uses ⟨gs,o⟩ := by
  intro i
  by_contra hn
  let u : Fin 11 := ⟨i.val,by omega⟩
  have h := insensitivity ⟨gs,o⟩ hb u hn (extended (flip i).1) (extended (flip i).2) (by
    intro j hj
    exact (flips i).1 j (fun e => hj (Fin.ext e)))
  change (Circuit.mk gs o).eval _ = (Circuit.mk gs o).eval _ at h
  rw [← early_eval, ← early_eval,he,he] at h
  exact (flips i).2 h
end PEqualNP.Research.Permanent27300

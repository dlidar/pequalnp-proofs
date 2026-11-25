import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Research.L_meta_2348_star_extension

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- Seven line stars on the cyclic Fano plane followed by six binary unions. -/
def stars : Circuit := ⟨[⟨.or, [0, 1]⟩,
   ⟨.or, [14, 3]⟩,
   ⟨.and, [15, 7]⟩,
   ⟨.or, [1, 2]⟩,
   ⟨.or, [17, 4]⟩,
   ⟨.and, [18, 8]⟩,
   ⟨.or, [2, 3]⟩,
   ⟨.or, [20, 5]⟩,
   ⟨.and, [21, 9]⟩,
   ⟨.or, [3, 4]⟩,
   ⟨.or, [23, 6]⟩,
   ⟨.and, [24, 10]⟩,
   ⟨.or, [4, 5]⟩,
   ⟨.or, [26, 0]⟩,
   ⟨.and, [27, 11]⟩,
   ⟨.or, [5, 6]⟩,
   ⟨.or, [29, 1]⟩,
   ⟨.and, [30, 12]⟩,
   ⟨.or, [6, 0]⟩,
   ⟨.or, [32, 2]⟩,
   ⟨.and, [33, 13]⟩,
   ⟨.or, [16, 19]⟩,
   ⟨.or, [35, 22]⟩,
   ⟨.or, [36, 25]⟩,
   ⟨.or, [37, 28]⟩,
   ⟨.or, [38, 31]⟩,
   ⟨.or, [39, 34]⟩], 40⟩


/-- The old-wire value on a single Fano flag and at its two endpoints. -/
def atInput (w : Fin 41) (xs : Fin 14 → Bool) : Bool := (stars.wires (List.ofFn xs)).getD w false
def lineIdx (t : Fin 7) : Fin 14 := Fin.natAdd 7 t
def ptIdx (u : Fin 7) : Fin 14 := Fin.castAdd 7 u
def edge (u t : Fin 7) (i : Fin 14) := decide (i = ptIdx u ∨ i = lineIdx t)
def inc (u t : Fin 7) : Bool := decide (u = t ∨ u = t + 1 ∨ u = t + 3)
def allPos (w : Fin 41) : Prop :=
  ∀ u t : Fin 7, inc u t = true → atInput w (edge u t) = true
instance (w : Fin 41) : Decidable (allPos w) := by unfold allPos; infer_instance

theorem unique_positive_cover : ∀ w : Fin 41, allPos w ↔ w = 40 := by decide +kernel

def single (w : Fin 41) (s : Bool) (u t : Fin 7) : Bool :=
  ((PEqualNP.ReadK.linearParts stars
    (fun i => i == (if s then (lineIdx t).val else (ptIdx u).val))
    ((List.range 14).map fun i => i == (ptIdx u).val || i == (lineIdx t).val)).getD w
    (false,false)).2

def own (w : Fin 41) (s : Bool) (u t : Fin 7) : Bool :=
  atInput w (fun i => decide (i = if s then ptIdx u else lineIdx t))

/-- An old wire that becomes true on the pair is either already true on the singleton
or has a parse with exactly one copy of the newly enabled input. -/
theorem old_pair (s : Bool) (w : Fin 41) (u t : Fin 7) (h : atInput w (edge u t) = true) :
    own w s u t || single w s u t := by
  revert h w u t s
  decide +kernel

/-- If an AND appended to this prefix is right on the 21 positive tests, its two
operands coincide with the old output. Thus distinct operands are impossible. -/
theorem and_operands_forced (a b : Fin 41)
    (h : ∀ u t : Fin 7, inc u t = true →
      (atInput a (edge u t) && atInput b (edge u t)) = true) :
    a = 40 ∧ b = 40 := by
  constructor
  · exact (unique_positive_cover a).mp fun u t e => (Bool.and_eq_true_iff.mp (h u t e)).1
  · exact (unique_positive_cover b).mp fun u t e => (Bool.and_eq_true_iff.mp (h u t e)).2

/-- If an appended OR is right on a flag and its two singletons, it preserves
a single-read parse in each orientation of that flag. -/
theorem or_preserves (a b : Fin 41) (u t : Fin 7)
    (hp : atInput a (edge u t) || atInput b (edge u t))
    (hn : ∀ s, (own a s u t || own b s u t) = false) :
    ∀ s : Bool, single a s u t || single b s u t := by
  intro s
  obtain ⟨ha,hb⟩ := Bool.or_eq_false_iff.mp (hn s)
  rcases Bool.or_eq_true_iff.mp hp with h | h
  · have d := old_pair s a u t h
    simp [ha] at d
    simp [d]
  · have d := old_pair s b u t h
    simp [hb] at d
    simp [d]

#print axioms and_operands_forced
#print axioms or_preserves
end PEqualNP.Research.L_meta_2348_star_extension

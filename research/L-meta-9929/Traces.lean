import Std.Tactic.BVDecide
import Mathlib.Tactic

namespace Comparator9929.Trace

abbrev Trace := BitVec 7
def falls (x : Trace) : Trace := x &&& ~~~(x >>> 1) &&& 63
def rises (x : Trace) : Trace := falls (~~~x)
abbrev Within (x mask : Trace) : Prop := x &&& ~~~mask = 0

inductive MonotoneBlock (sources : Trace → Prop) : Trace → Prop where
  | raw {x} : sources x → MonotoneBlock sources x
  | zero : MonotoneBlock sources 0
  | one : MonotoneBlock sources 127
  | conj {x y} : MonotoneBlock sources x → MonotoneBlock sources y →
      MonotoneBlock sources (x &&& y)
  | disj {x y} : MonotoneBlock sources x → MonotoneBlock sources y →
      MonotoneBlock sources (x ||| y)

private theorem check_and (a b m : Trace)
    (ha : Within (falls a) m) (hb : Within (falls b) m) :
    Within (falls (a &&& b)) m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := congrArg (fun v : Trace => v.getLsbD i) ha
  have h2 := congrArg (fun v : Trace => v.getLsbD i) hb
  simp only [Within, falls, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and] at *
  revert h1 h2
  generalize a.getLsbD i = u
  generalize b.getLsbD i = v
  generalize a.getLsbD (1+i) = w
  generalize b.getLsbD (1+i) = x
  generalize (63:Trace).getLsbD i = y
  generalize m.getLsbD i = z
  generalize (0:Trace).getLsbD i = rhs
  decide +revert

private theorem check_or (a b m : Trace)
    (ha : Within (falls a) m) (hb : Within (falls b) m) :
    Within (falls (a ||| b)) m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := congrArg (fun v : Trace => v.getLsbD i) ha
  have h2 := congrArg (fun v : Trace => v.getLsbD i) hb
  simp only [Within, falls, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and] at *
  revert h1 h2
  generalize a.getLsbD i = u
  generalize b.getLsbD i = v
  generalize a.getLsbD (1+i) = w
  generalize b.getLsbD (1+i) = x
  generalize (63:Trace).getLsbD i = y
  generalize m.getLsbD i = z
  generalize (0:Trace).getLsbD i = rhs
  decide +revert

theorem block_falls {s : Trace → Prop} {out mask : Trace}
    (h : MonotoneBlock s out) (bound : ∀ x, s x → Within (falls x) mask) :
    Within (falls out) mask := by
  induction h with
  | raw h => exact bound _ h
  | zero => simp [Within, falls]
  | one => change (0 : Trace) &&& _ = 0; simp
  | conj _ _ ha hb => exact check_and _ _ _ ha hb
  | disj _ _ ha hb => exact check_or _ _ _ ha hb

def Ascending (x : Trace) : Prop := falls x = 0

private theorem selfWithin (x : Trace) : Within x x := by
  revert x
  decide
private theorem leftWithin (x y : Trace) : Within x (x ||| y) := by
  revert x y
  decide
private theorem rightWithin (x y : Trace) : Within y (x ||| y) := by
  rw [BitVec.or_comm]
  exact leftWithin _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem finite_patterns : ∀ a b : Trace,
    Within (falls a) 0 → Within (falls b) (rises a) →
    Within (falls 42) (rises a ||| rises b) → a = 112 ∧ b = 76 := by decide

theorem two_inverters (first second : Trace)
    (h₁ : MonotoneBlock Ascending first)
    (h₂ : MonotoneBlock (fun x => Ascending x ∨ x = ~~~first) second)
    (hout : MonotoneBlock (fun x => Ascending x ∨ x = ~~~first ∨ x = ~~~second) 42) :
    first = 112 ∧ second = 76 := by
  have b₁ : Within (falls first) 0 := block_falls h₁ (by
    intro x h
    change falls x = 0 at h
    simp [Within, h])
  have b₂ : Within (falls second) (rises first) := block_falls h₂ (by
    rintro x (hx | rfl)
    · change falls x = 0 at hx
      simp [Within, hx]
    · exact selfWithin _)
  have b₃ : Within (falls 42) (rises first ||| rises second) := block_falls hout (by
    rintro x (hx | rfl | rfl)
    · change falls x = 0 at hx
      simp [Within, hx]
    · exact leftWithin _ _
    · exact rightWithin _ _)
  exact finite_patterns first second b₁ b₂ b₃

theorem one_inverter_impossible (first : Trace) (h : MonotoneBlock Ascending first)
    (hout : MonotoneBlock (fun x => Ascending x ∨ x = ~~~first) 42) : False := by
  have h₂ : MonotoneBlock (fun x => Ascending x ∨ x = ~~~first) 0 := .zero
  have wide : MonotoneBlock (fun x => Ascending x ∨ x = ~~~first ∨ x = ~~~(0:Trace)) 42 := by
    generalize hy : (42 : Trace) = y at hout ⊢
    clear hy
    induction hout with
    | raw h => exact .raw (h.imp_right Or.inl)
    | zero => exact .zero
    | one => exact .one
    | conj _ _ a b => exact .conj a b
    | disj _ _ a b => exact .disj a b
  have hbad := (two_inverters first 0 h h₂ wide).2
  contradiction
#print axioms block_falls
#print axioms two_inverters
#print axioms one_inverter_impossible
end Comparator9929.Trace

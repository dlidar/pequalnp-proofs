import Mathlib
import PEqualNP.Defs.MetaComplexity

namespace PEqualNP.Research.BridgeTriangles

abbrev Word := BitVec 16
def localHit (a b c u : Bool) := (b && c) || (a && (b || c || u))
def graph (a b c u v d e f : Bool) :=
  localHit a b c u || localHit d e f v || (u && v)

theorem graph_eq (a b c u v d e f : Bool) :
  graph a b c u v d e f =
  ((a && b) || (a && c) || (a && u) || (b && c) || (u && v) ||
   (v && d) || (d && e) || (d && f) || (e && f)) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases d <;>
    cases e <;> cases f <;> rfl

def leftHit : Word := 60136
def leftArmed : Word := 65512

-- The two right-hand probes are the empty input and just the bridge endpoint.
theorem probe_masks : ∀ r : Fin 16,
  let a := r.val.testBit 0
  let b := r.val.testBit 1
  let c := r.val.testBit 2
  let u := r.val.testBit 3
  graph a b c u false false false false = leftHit.getLsbD r.val ∧
  graph a b c u true false false false = leftArmed.getLsbD r.val := by decide +kernel

def initial : List Word := [43690, 52428, 61680, 65280, 0, 65535]

def moves (s : List Word) : List Word :=
  ((s.map (fun x => ~~~x)) ++ (s.flatMap (fun x =>
    s.flatMap (fun y => [x &&& y, x ||| y])))).eraseDups.filter (fun x => x ∉ s)

def uniform (m t : Word) : Bool := (m &&& t == 0) || (m &&& t == m)

def cellOK (m : Word) : Bool := uniform m leftHit && uniform m leftArmed

def separates (x y : Word) : Bool :=
  cellOK (x &&& y) && cellOK (x &&& ~~~y) &&
  cellOK (~~~x &&& y) && cellOK (~~~x &&& ~~~y)

def safeMore : Nat → List Word → Bool
  | 0, _ => true
  | n+1, s => (moves s).all (fun z =>
      (z :: s).all (fun y => !separates z y) && safeMore n (z :: s))

def safe (s : List Word) : Prop := ∀ x ∈ s, ∀ y ∈ s, separates x y = false

theorem initial_safe : safe initial := by
  have h : initial.all (fun x => initial.all (fun y => !separates x y)) = true := by decide +kernel
  simpa [safe,List.all_eq_true] using h

private theorem case_255_170 : safeMore 2 (170 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_204 : safeMore 2 (204 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_240 : safeMore 2 (240 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_3855 : safeMore 2 (3855 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_13107 : safeMore 2 (13107 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_21845 : safeMore 2 (21845 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_34952 : safeMore 2 (34952 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_41120 : safeMore 2 (41120 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_43520 : safeMore 2 (43520 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_43775 : safeMore 2 (43775 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_49344 : safeMore 2 (49344 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_52224 : safeMore 2 (52224 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_52479 : safeMore 2 (52479 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_61166 : safeMore 2 (61166 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_61440 : safeMore 2 (61440 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_61695 : safeMore 2 (61695 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_64250 : safeMore 2 (64250 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_64764 : safeMore 2 (64764 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_65450 : safeMore 2 (65450 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_65484 : safeMore 2 (65484 :: 255 :: initial) = true := by decide +kernel
private theorem case_255_65520 : safeMore 2 (65520 :: 255 :: initial) = true := by decide +kernel
private theorem first_255 : safeMore 3 (255 :: initial) = true := by
  have sub : moves (255 :: initial) ⊆ ([170, 204, 240, 3855, 13107, 21845, 34952, 41120, 43520, 43775, 49344, 52224, 52479, 61166, 61440, 61695, 64250, 64764, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_170⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_204⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_240⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_43775⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_52479⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_61695⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_255_65520⟩
private theorem case_3855_255 : safeMore 2 (255 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_2570 : safeMore 2 (2570 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_3084 : safeMore 2 (3084 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_3840 : safeMore 2 (3840 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_13107 : safeMore 2 (13107 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_21845 : safeMore 2 (21845 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_34952 : safeMore 2 (34952 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_41120 : safeMore 2 (41120 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_43520 : safeMore 2 (43520 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_44975 : safeMore 2 (44975 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_49344 : safeMore 2 (49344 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_52224 : safeMore 2 (52224 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_53199 : safeMore 2 (53199 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_61166 : safeMore 2 (61166 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_61440 : safeMore 2 (61440 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_64250 : safeMore 2 (64250 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_64764 : safeMore 2 (64764 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_65295 : safeMore 2 (65295 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_65450 : safeMore 2 (65450 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_65484 : safeMore 2 (65484 :: 3855 :: initial) = true := by decide +kernel
private theorem case_3855_65520 : safeMore 2 (65520 :: 3855 :: initial) = true := by decide +kernel
private theorem first_3855 : safeMore 3 (3855 :: initial) = true := by
  have sub : moves (3855 :: initial) ⊆ ([255, 2570, 3084, 3840, 13107, 21845, 34952, 41120, 43520, 44975, 49344, 52224, 53199, 61166, 61440, 64250, 64764, 65295, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_2570⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_3084⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_3840⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_44975⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_53199⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_65295⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_3855_65520⟩
private theorem case_13107_255 : safeMore 2 (255 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_3855 : safeMore 2 (3855 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_8738 : safeMore 2 (8738 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_12336 : safeMore 2 (12336 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_13056 : safeMore 2 (13056 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_21845 : safeMore 2 (21845 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_34952 : safeMore 2 (34952 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_41120 : safeMore 2 (41120 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_43520 : safeMore 2 (43520 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_48059 : safeMore 2 (48059 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_49344 : safeMore 2 (49344 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_52224 : safeMore 2 (52224 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_61166 : safeMore 2 (61166 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_61440 : safeMore 2 (61440 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_62451 : safeMore 2 (62451 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_64250 : safeMore 2 (64250 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_64764 : safeMore 2 (64764 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_65331 : safeMore 2 (65331 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_65450 : safeMore 2 (65450 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_65484 : safeMore 2 (65484 :: 13107 :: initial) = true := by decide +kernel
private theorem case_13107_65520 : safeMore 2 (65520 :: 13107 :: initial) = true := by decide +kernel
private theorem first_13107 : safeMore 3 (13107 :: initial) = true := by
  have sub : moves (13107 :: initial) ⊆ ([255, 3855, 8738, 12336, 13056, 21845, 34952, 41120, 43520, 48059, 49344, 52224, 61166, 61440, 62451, 64250, 64764, 65331, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_8738⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_12336⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_13056⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_48059⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_62451⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_65331⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_13107_65520⟩
private theorem case_21845_255 : safeMore 2 (255 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_3855 : safeMore 2 (3855 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_13107 : safeMore 2 (13107 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_17476 : safeMore 2 (17476 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_20560 : safeMore 2 (20560 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_21760 : safeMore 2 (21760 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_34952 : safeMore 2 (34952 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_41120 : safeMore 2 (41120 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_43520 : safeMore 2 (43520 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_49344 : safeMore 2 (49344 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_52224 : safeMore 2 (52224 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_56797 : safeMore 2 (56797 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_61166 : safeMore 2 (61166 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_61440 : safeMore 2 (61440 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_62965 : safeMore 2 (62965 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_64250 : safeMore 2 (64250 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_64764 : safeMore 2 (64764 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_65365 : safeMore 2 (65365 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_65450 : safeMore 2 (65450 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_65484 : safeMore 2 (65484 :: 21845 :: initial) = true := by decide +kernel
private theorem case_21845_65520 : safeMore 2 (65520 :: 21845 :: initial) = true := by decide +kernel
private theorem first_21845 : safeMore 3 (21845 :: initial) = true := by
  have sub : moves (21845 :: initial) ⊆ ([255, 3855, 13107, 17476, 20560, 21760, 34952, 41120, 43520, 49344, 52224, 56797, 61166, 61440, 62965, 64250, 64764, 65365, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_17476⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_20560⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_21760⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_56797⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_62965⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_65365⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_21845_65520⟩
private theorem case_34952_255 : safeMore 2 (255 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_3855 : safeMore 2 (3855 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_13107 : safeMore 2 (13107 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_21845 : safeMore 2 (21845 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_30583 : safeMore 2 (30583 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_32896 : safeMore 2 (32896 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_34816 : safeMore 2 (34816 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_41120 : safeMore 2 (41120 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_43520 : safeMore 2 (43520 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_49344 : safeMore 2 (49344 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_52224 : safeMore 2 (52224 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_61166 : safeMore 2 (61166 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_61440 : safeMore 2 (61440 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_63736 : safeMore 2 (63736 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_64250 : safeMore 2 (64250 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_64764 : safeMore 2 (64764 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_65416 : safeMore 2 (65416 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_65450 : safeMore 2 (65450 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_65484 : safeMore 2 (65484 :: 34952 :: initial) = true := by decide +kernel
private theorem case_34952_65520 : safeMore 2 (65520 :: 34952 :: initial) = true := by decide +kernel
private theorem first_34952 : safeMore 3 (34952 :: initial) = true := by
  have sub : moves (34952 :: initial) ⊆ ([255, 3855, 13107, 21845, 30583, 32896, 34816, 41120, 43520, 49344, 52224, 61166, 61440, 63736, 64250, 64764, 65416, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_30583⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_32896⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_34816⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_63736⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_65416⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_34952_65520⟩
private theorem case_41120_255 : safeMore 2 (255 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_3855 : safeMore 2 (3855 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_13107 : safeMore 2 (13107 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_21845 : safeMore 2 (21845 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_24415 : safeMore 2 (24415 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_32896 : safeMore 2 (32896 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_34952 : safeMore 2 (34952 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_40960 : safeMore 2 (40960 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_43520 : safeMore 2 (43520 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_49344 : safeMore 2 (49344 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_52224 : safeMore 2 (52224 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_60652 : safeMore 2 (60652 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_61166 : safeMore 2 (61166 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_61440 : safeMore 2 (61440 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_64250 : safeMore 2 (64250 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_64764 : safeMore 2 (64764 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_65440 : safeMore 2 (65440 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_65450 : safeMore 2 (65450 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_65484 : safeMore 2 (65484 :: 41120 :: initial) = true := by decide +kernel
private theorem case_41120_65520 : safeMore 2 (65520 :: 41120 :: initial) = true := by decide +kernel
private theorem first_41120 : safeMore 3 (41120 :: initial) = true := by
  have sub : moves (41120 :: initial) ⊆ ([255, 3855, 13107, 21845, 24415, 32896, 34952, 40960, 43520, 49344, 52224, 60652, 61166, 61440, 64250, 64764, 65440, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_24415⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_32896⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_40960⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_60652⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_65440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_41120_65520⟩
private theorem case_43520_255 : safeMore 2 (255 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_3855 : safeMore 2 (3855 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_13107 : safeMore 2 (13107 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_21845 : safeMore 2 (21845 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_22015 : safeMore 2 (22015 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_34816 : safeMore 2 (34816 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_34952 : safeMore 2 (34952 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_40960 : safeMore 2 (40960 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_41120 : safeMore 2 (41120 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_49344 : safeMore 2 (49344 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_52224 : safeMore 2 (52224 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_61132 : safeMore 2 (61132 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_61166 : safeMore 2 (61166 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_61440 : safeMore 2 (61440 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_64240 : safeMore 2 (64240 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_64250 : safeMore 2 (64250 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_64764 : safeMore 2 (64764 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_65450 : safeMore 2 (65450 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_65484 : safeMore 2 (65484 :: 43520 :: initial) = true := by decide +kernel
private theorem case_43520_65520 : safeMore 2 (65520 :: 43520 :: initial) = true := by decide +kernel
private theorem first_43520 : safeMore 3 (43520 :: initial) = true := by
  have sub : moves (43520 :: initial) ⊆ ([255, 3855, 13107, 21845, 22015, 34816, 34952, 40960, 41120, 49344, 52224, 61132, 61166, 61440, 64240, 64250, 64764, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_22015⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_34816⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_40960⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_61132⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_64240⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_43520_65520⟩
private theorem case_49344_255 : safeMore 2 (255 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_3855 : safeMore 2 (3855 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_13107 : safeMore 2 (13107 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_16191 : safeMore 2 (16191 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_21845 : safeMore 2 (21845 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_32896 : safeMore 2 (32896 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_34952 : safeMore 2 (34952 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_41120 : safeMore 2 (41120 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_43520 : safeMore 2 (43520 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_49152 : safeMore 2 (49152 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_52224 : safeMore 2 (52224 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_60138 : safeMore 2 (60138 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_61166 : safeMore 2 (61166 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_61440 : safeMore 2 (61440 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_64250 : safeMore 2 (64250 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_64764 : safeMore 2 (64764 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_65450 : safeMore 2 (65450 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_65472 : safeMore 2 (65472 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_65484 : safeMore 2 (65484 :: 49344 :: initial) = true := by decide +kernel
private theorem case_49344_65520 : safeMore 2 (65520 :: 49344 :: initial) = true := by decide +kernel
private theorem first_49344 : safeMore 3 (49344 :: initial) = true := by
  have sub : moves (49344 :: initial) ⊆ ([255, 3855, 13107, 16191, 21845, 32896, 34952, 41120, 43520, 49152, 52224, 60138, 61166, 61440, 64250, 64764, 65450, 65472, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_16191⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_32896⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_49152⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_60138⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_65472⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_49344_65520⟩
private theorem case_52224_255 : safeMore 2 (255 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_3855 : safeMore 2 (3855 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_13107 : safeMore 2 (13107 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_13311 : safeMore 2 (13311 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_21845 : safeMore 2 (21845 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_34816 : safeMore 2 (34816 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_34952 : safeMore 2 (34952 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_41120 : safeMore 2 (41120 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_43520 : safeMore 2 (43520 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_49152 : safeMore 2 (49152 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_49344 : safeMore 2 (49344 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_61098 : safeMore 2 (61098 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_61166 : safeMore 2 (61166 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_61440 : safeMore 2 (61440 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_64250 : safeMore 2 (64250 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_64752 : safeMore 2 (64752 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_64764 : safeMore 2 (64764 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_65450 : safeMore 2 (65450 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_65484 : safeMore 2 (65484 :: 52224 :: initial) = true := by decide +kernel
private theorem case_52224_65520 : safeMore 2 (65520 :: 52224 :: initial) = true := by decide +kernel
private theorem first_52224 : safeMore 3 (52224 :: initial) = true := by
  have sub : moves (52224 :: initial) ⊆ ([255, 3855, 13107, 13311, 21845, 34816, 34952, 41120, 43520, 49152, 49344, 61098, 61166, 61440, 64250, 64752, 64764, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_13311⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_34816⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_49152⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_61098⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_64752⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_52224_65520⟩
private theorem case_61166_255 : safeMore 2 (255 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_3855 : safeMore 2 (3855 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_4369 : safeMore 2 (4369 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_13107 : safeMore 2 (13107 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_21845 : safeMore 2 (21845 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_34952 : safeMore 2 (34952 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_41120 : safeMore 2 (41120 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_43520 : safeMore 2 (43520 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_49344 : safeMore 2 (49344 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_52224 : safeMore 2 (52224 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_57568 : safeMore 2 (57568 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_60928 : safeMore 2 (60928 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_61440 : safeMore 2 (61440 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_64250 : safeMore 2 (64250 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_64764 : safeMore 2 (64764 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_65278 : safeMore 2 (65278 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_65450 : safeMore 2 (65450 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_65484 : safeMore 2 (65484 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_65518 : safeMore 2 (65518 :: 61166 :: initial) = true := by decide +kernel
private theorem case_61166_65520 : safeMore 2 (65520 :: 61166 :: initial) = true := by decide +kernel
private theorem first_61166 : safeMore 3 (61166 :: initial) = true := by
  have sub : moves (61166 :: initial) ⊆ ([255, 3855, 4369, 13107, 21845, 34952, 41120, 43520, 49344, 52224, 57568, 60928, 61440, 64250, 64764, 65278, 65450, 65484, 65518, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_4369⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_57568⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_60928⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_65278⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_65518⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61166_65520⟩
private theorem case_61440_255 : safeMore 2 (255 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_3855 : safeMore 2 (3855 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_4095 : safeMore 2 (4095 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_13107 : safeMore 2 (13107 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_21845 : safeMore 2 (21845 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_34952 : safeMore 2 (34952 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_40960 : safeMore 2 (40960 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_41120 : safeMore 2 (41120 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_43520 : safeMore 2 (43520 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_49152 : safeMore 2 (49152 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_49344 : safeMore 2 (49344 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_52224 : safeMore 2 (52224 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_61166 : safeMore 2 (61166 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_64170 : safeMore 2 (64170 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_64250 : safeMore 2 (64250 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_64716 : safeMore 2 (64716 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_64764 : safeMore 2 (64764 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_65450 : safeMore 2 (65450 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_65484 : safeMore 2 (65484 :: 61440 :: initial) = true := by decide +kernel
private theorem case_61440_65520 : safeMore 2 (65520 :: 61440 :: initial) = true := by decide +kernel
private theorem first_61440 : safeMore 3 (61440 :: initial) = true := by
  have sub : moves (61440 :: initial) ⊆ ([255, 3855, 4095, 13107, 21845, 34952, 40960, 41120, 43520, 49152, 49344, 52224, 61166, 64170, 64250, 64716, 64764, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_4095⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_40960⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_49152⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_64170⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_64716⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_61440_65520⟩
private theorem case_64250_255 : safeMore 2 (255 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_1285 : safeMore 2 (1285 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_3855 : safeMore 2 (3855 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_13107 : safeMore 2 (13107 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_21845 : safeMore 2 (21845 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_34952 : safeMore 2 (34952 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_41120 : safeMore 2 (41120 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_43520 : safeMore 2 (43520 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_49344 : safeMore 2 (49344 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_51400 : safeMore 2 (51400 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_52224 : safeMore 2 (52224 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_61166 : safeMore 2 (61166 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_61440 : safeMore 2 (61440 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_64000 : safeMore 2 (64000 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_64764 : safeMore 2 (64764 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_65278 : safeMore 2 (65278 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_65450 : safeMore 2 (65450 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_65484 : safeMore 2 (65484 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_65520 : safeMore 2 (65520 :: 64250 :: initial) = true := by decide +kernel
private theorem case_64250_65530 : safeMore 2 (65530 :: 64250 :: initial) = true := by decide +kernel
private theorem first_64250 : safeMore 3 (64250 :: initial) = true := by
  have sub : moves (64250 :: initial) ⊆ ([255, 1285, 3855, 13107, 21845, 34952, 41120, 43520, 49344, 51400, 52224, 61166, 61440, 64000, 64764, 65278, 65450, 65484, 65520, 65530] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_1285⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_51400⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_64000⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_65278⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_65520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64250_65530⟩
private theorem case_64764_255 : safeMore 2 (255 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_771 : safeMore 2 (771 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_3855 : safeMore 2 (3855 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_13107 : safeMore 2 (13107 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_21845 : safeMore 2 (21845 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_34952 : safeMore 2 (34952 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_41120 : safeMore 2 (41120 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_43176 : safeMore 2 (43176 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_43520 : safeMore 2 (43520 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_49344 : safeMore 2 (49344 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_52224 : safeMore 2 (52224 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_61166 : safeMore 2 (61166 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_61440 : safeMore 2 (61440 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_64250 : safeMore 2 (64250 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_64512 : safeMore 2 (64512 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_65278 : safeMore 2 (65278 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_65450 : safeMore 2 (65450 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_65484 : safeMore 2 (65484 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_65520 : safeMore 2 (65520 :: 64764 :: initial) = true := by decide +kernel
private theorem case_64764_65532 : safeMore 2 (65532 :: 64764 :: initial) = true := by decide +kernel
private theorem first_64764 : safeMore 3 (64764 :: initial) = true := by
  have sub : moves (64764 :: initial) ⊆ ([255, 771, 3855, 13107, 21845, 34952, 41120, 43176, 43520, 49344, 52224, 61166, 61440, 64250, 64512, 65278, 65450, 65484, 65520, 65532] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_771⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_43176⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_64512⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_65278⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_65520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_64764_65532⟩
private theorem case_65450_85 : safeMore 2 (85 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_255 : safeMore 2 (255 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_3855 : safeMore 2 (3855 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_13107 : safeMore 2 (13107 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_21845 : safeMore 2 (21845 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_34952 : safeMore 2 (34952 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_41120 : safeMore 2 (41120 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_43520 : safeMore 2 (43520 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_49344 : safeMore 2 (49344 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_52224 : safeMore 2 (52224 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_52360 : safeMore 2 (52360 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_61166 : safeMore 2 (61166 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_61440 : safeMore 2 (61440 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_61600 : safeMore 2 (61600 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_64250 : safeMore 2 (64250 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_64764 : safeMore 2 (64764 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_65484 : safeMore 2 (65484 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_65518 : safeMore 2 (65518 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_65520 : safeMore 2 (65520 :: 65450 :: initial) = true := by decide +kernel
private theorem case_65450_65530 : safeMore 2 (65530 :: 65450 :: initial) = true := by decide +kernel
private theorem first_65450 : safeMore 3 (65450 :: initial) = true := by
  have sub : moves (65450 :: initial) ⊆ ([85, 255, 3855, 13107, 21845, 34952, 41120, 43520, 49344, 52224, 52360, 61166, 61440, 61600, 64250, 64764, 65484, 65518, 65520, 65530] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_85⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_52360⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_61600⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_65518⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_65520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65450_65530⟩
private theorem case_65484_51 : safeMore 2 (51 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_255 : safeMore 2 (255 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_3855 : safeMore 2 (3855 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_13107 : safeMore 2 (13107 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_21845 : safeMore 2 (21845 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_34952 : safeMore 2 (34952 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_41120 : safeMore 2 (41120 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_43520 : safeMore 2 (43520 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_43656 : safeMore 2 (43656 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_49344 : safeMore 2 (49344 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_52224 : safeMore 2 (52224 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_61166 : safeMore 2 (61166 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_61440 : safeMore 2 (61440 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_61632 : safeMore 2 (61632 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_64250 : safeMore 2 (64250 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_64764 : safeMore 2 (64764 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_65450 : safeMore 2 (65450 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_65518 : safeMore 2 (65518 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_65520 : safeMore 2 (65520 :: 65484 :: initial) = true := by decide +kernel
private theorem case_65484_65532 : safeMore 2 (65532 :: 65484 :: initial) = true := by decide +kernel
private theorem first_65484 : safeMore 3 (65484 :: initial) = true := by
  have sub : moves (65484 :: initial) ⊆ ([51, 255, 3855, 13107, 21845, 34952, 41120, 43520, 43656, 49344, 52224, 61166, 61440, 61632, 64250, 64764, 65450, 65518, 65520, 65532] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_51⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_43656⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_61632⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_65518⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_65520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65484_65532⟩
private theorem case_65520_15 : safeMore 2 (15 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_255 : safeMore 2 (255 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_3855 : safeMore 2 (3855 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_13107 : safeMore 2 (13107 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_21845 : safeMore 2 (21845 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_34952 : safeMore 2 (34952 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_41120 : safeMore 2 (41120 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_43520 : safeMore 2 (43520 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_43680 : safeMore 2 (43680 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_49344 : safeMore 2 (49344 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_52224 : safeMore 2 (52224 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_52416 : safeMore 2 (52416 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_61166 : safeMore 2 (61166 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_61440 : safeMore 2 (61440 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_64250 : safeMore 2 (64250 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_64764 : safeMore 2 (64764 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_65450 : safeMore 2 (65450 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_65484 : safeMore 2 (65484 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_65530 : safeMore 2 (65530 :: 65520 :: initial) = true := by decide +kernel
private theorem case_65520_65532 : safeMore 2 (65532 :: 65520 :: initial) = true := by decide +kernel
private theorem first_65520 : safeMore 3 (65520 :: initial) = true := by
  have sub : moves (65520 :: initial) ⊆ ([15, 255, 3855, 13107, 21845, 34952, 41120, 43520, 43680, 49344, 52224, 52416, 61166, 61440, 64250, 64764, 65450, 65484, 65530, 65532] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_15⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_43680⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_52416⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_65530⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, case_65520_65532⟩
theorem four_safe : safeMore 4 (initial) = true := by
  have sub : moves (initial) ⊆ ([255, 3855, 13107, 21845, 34952, 41120, 43520, 49344, 52224, 61166, 61440, 64250, 64764, 65450, 65484, 65520] : List Word) := by decide +kernel
  rw [safeMore,List.all_eq_true]
  intro w hw
  have hm := sub hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_255⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_3855⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_13107⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_21845⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_34952⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_41120⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_43520⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_49344⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_52224⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_61166⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_61440⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_64250⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_64764⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_65450⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_65484⟩
  · exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, first_65520⟩

-- A run records newly available truth tables. Copies and redundant gates can be omitted.
inductive Run : Nat → List Word → List Word → Prop
  | done {n s} : Run n s s
  | add {n s t z} : z ∈ moves s → Run n (z :: s) t → Run (n+1) s t

theorem mem_moves (s : List Word) {x y : Word} (hx : x ∈ s) (hy : y ∈ s) :
    ∀ z ∈ [~~~x, x &&& y, x ||| y], z ∈ s ∨ z ∈ moves s := by
  intro z hz
  by_cases h : z ∈ s
  · exact Or.inl h
  right
  simp only [moves, List.mem_filter, List.mem_eraseDups, List.mem_append, List.mem_map,
    List.mem_flatMap, decide_eq_true_eq, h, not_false_eq_true, and_true]
  rcases List.mem_cons.mp hz with rfl | hz
  · exact Or.inl ⟨x,hx,rfl⟩
  · exact Or.inr ⟨x,hx,y,hy,hz⟩

theorem sep_comm (x y : Word) : separates x y = separates y x := by
  simp only [separates, BitVec.and_comm y x, BitVec.and_comm y (~~~x),
    BitVec.and_comm (~~~y) x, BitVec.and_comm (~~~y) (~~~x)]
  ac_rfl

theorem run_safe {k b : Nat} {s t : List Word}
    (run : Run k s t) (hk : k ≤ b) (hs : safe s) (hb : safeMore b s = true) : safe t := by
  induction run generalizing b with
  | done => exact hs
  | @add n s t z hm _ ih =>
    cases b with
    | zero => omega
    | succ b =>
      have hn0 := (List.all_eq_true.mp hb) z hm
      simp only [Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true'] at hn0
      obtain ⟨hn,hb'⟩ := hn0
      apply ih (b := b) (by omega) _ hb'
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl|hx <;> rcases List.mem_cons.mp hy with rfl|hy
      · exact hn _ (by simp)
      · exact hn _ (by simp [hy])
      · rw [sep_comm]; exact hn _ (by simp [hx])
      · exact hs _ hx _ hy

theorem five_local_gates {n : Nat} {s : List Word} {x y : Word}
    (run : Run n initial s) (hx : x ∈ s) (hy : y ∈ s) (ok : separates x y = true) : 5 ≤ n := by
  by_contra! h
  have hn := run_safe run (b := 4) (by omega) initial_safe four_safe x hx y hy
  simp_all

def region (x y : Word) (a b : Bool) : Word :=
  (if a then x else ~~~x) &&& (if b then y else ~~~y)

theorem uniform_of_decoder (x y target : Word) (f : Bool → Bool → Bool)
    (h : ∀ i : Fin 16, target.getLsbD i.val = f (x.getLsbD i.val) (y.getLsbD i.val))
    (a b : Bool) : uniform (region x y a b) target = true := by
  let m := region x y a b
  have hm (i : Nat) (hi : i < 16) (hm' : m.getLsbD i = true) :
      x.getLsbD i = a ∧ y.getLsbD i = b := by
    cases a <;> cases b <;> simp_all [m,region]
  cases hf : f a b with
  | false =>
    have hz : m &&& target = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases hh : m.getLsbD i with
      | false => simp [hh]
      | true => obtain ⟨hx,hy⟩ := hm i hi hh; simp [hh,h ⟨i,hi⟩,hx,hy,hf]
    simp [uniform,← show m = region x y a b from rfl,hz]
  | true =>
    have hz : m &&& target = m := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases hh : m.getLsbD i with
      | false => simp [hh]
      | true => obtain ⟨hx,hy⟩ := hm i hi hh; simp [hh,h ⟨i,hi⟩,hx,hy,hf]
    simp [uniform,← show m = region x y a b from rfl,hz]

theorem separates_of_probes (x y : Word) (f g : Bool → Bool → Bool)
    (h : ∀ i : Fin 16, leftHit.getLsbD i.val = f (x.getLsbD i.val) (y.getLsbD i.val))
    (h' : ∀ i : Fin 16, leftArmed.getLsbD i.val = g (x.getLsbD i.val) (y.getLsbD i.val)) :
    separates x y = true := by
  have hc (a b : Bool) : cellOK (region x y a b) = true :=
    by simp [cellOK,uniform_of_decoder _ _ _ f h a b,uniform_of_decoder _ _ _ g h' a b]
  change (cellOK (region x y true true) && cellOK (region x y true false) &&
    cellOK (region x y false true) && cellOK (region x y false false)) = true
  simp [hc]

def matrix (i j : Fin 3) : Bool := decide (i.val+j.val ≥ 2)
def feature (left : Bool) (p : Fin 3 → Bool) (i j : Fin 3) := if left then p i else p j

theorem one_bit_rows {T : Type} (p : Fin 3 → Bool) (q : Fin 3 → T) (d : Bool → T → Bool)
    (h : ∀ i j, d (p i) (q j) = matrix i j) : False := by
  have hd {i j : Fin 3} (e : p i = p j) (t : Fin 3) : matrix i t = matrix j t := by
    rw [← h, ← h, e]
  have h01 : p 0 ≠ p 1 := fun e => (by decide : matrix 0 1 ≠ matrix 1 1) (hd e 1)
  have h12 : p 1 ≠ p 2 := fun e => (by decide : matrix 1 0 ≠ matrix 2 0) (hd e 0)
  have h02 : p 0 ≠ p 2 := fun e => (by decide : matrix 0 0 ≠ matrix 2 0) (hd e 0)
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> simp_all

theorem one_bit_cols {T : Type} (q : Fin 3 → T) (p : Fin 3 → Bool) (d : T → Bool → Bool)
    (h : ∀ i j, d (q i) (p j) = matrix i j) : False :=
  one_bit_rows p q (fun x y => d y x) (fun i j => by simpa [matrix,Nat.add_comm] using h j i)

-- Every tree of at most two binary gates uses at most three source wires.
theorem three_features (l m n : Bool) (p q r : Fin 3 → Bool) (D : Bool → Bool → Bool → Bool)
    (h : ∀ i j, D (feature l p i j) (feature m q i j) (feature n r i j) = matrix i j) : False := by
  cases l <;> cases m <;> cases n <;> simp only [feature, Bool.false_eq_true, ite_false, ite_true] at h
  · exact one_bit_rows (fun _ => false) id (fun _ j => D (p j) (q j) (r j)) h
  · exact one_bit_rows r id (fun x j => D (p j) (q j) x) h
  · exact one_bit_rows q id (fun x j => D (p j) x (r j)) h
  · exact one_bit_cols id p (fun i x => D x (q i) (r i)) h
  · exact one_bit_rows p id (fun x j => D x (q j) (r j)) h
  · exact one_bit_cols id q (fun i x => D (p i) x (r i)) h
  · exact one_bit_cols id r (fun i x => D (p i) (q i) x) h
  · exact one_bit_cols id (fun _ => false) (fun i _ => D (p i) (q i) (r i)) h

def sample (i : Fin 3) : Bool × Bool × Bool × Bool :=
  if i = 0 then (false,false,false,false) else
  if i = 1 then (false,false,false,true) else (true,true,false,false)

theorem sample_matrix : ∀ i j : Fin 3,
  let (a,b,c,u) := sample i
  let (d,e,f,v) := sample j
  graph a b c u v d e f = matrix i j := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem thirteen : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x =>
  graph (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or,[1,2]⟩,⟨.or,[3,8]⟩,⟨.and,[0,9]⟩,⟨.and,[1,2]⟩,⟨.or,[10,11]⟩,
    ⟨.or,[6,7]⟩,⟨.or,[4,13]⟩,⟨.and,[5,14]⟩,⟨.and,[6,7]⟩,⟨.or,[15,16]⟩,
    ⟨.and,[3,4]⟩,⟨.or,[12,17]⟩,⟨.or,[18,19]⟩],20⟩
  refine ⟨C,?_,by decide +kernel,?_⟩
  · intro gate hg
    change gate ∈ C.gates at hg
    simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

end PEqualNP.Research.BridgeTriangles

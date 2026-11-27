import Traces
namespace Comparator9929.Paths
open Comparator9929.Trace
abbrev Table := BitVec 64
abbrev Path := Fin 7 → Fin 64
def restrict (p : Path) (x : Table) : Trace := BitVec.ofBoolListLE [x.getLsbD (p 0), x.getLsbD (p 1), x.getLsbD (p 2), x.getLsbD (p 3), x.getLsbD (p 4), x.getLsbD (p 5), x.getLsbD (p 6)]
theorem at_bit (p : Path) (x : Table) (i : Fin 7) :
    (restrict p x).getLsbD i = x.getLsbD (p i) := by
  fin_cases i <;> unfold restrict <;> rw [BitVec.getLsbD_ofBoolListLE] <;> rfl

private theorem bit_eq {x y : Trace} (h : ∀ i : Fin 7, x.getLsbD i = y.getLsbD i) :
    x = y := BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i,hi⟩)
theorem map_and (p : Path) (x y : Table) :
    restrict p (x &&& y) = restrict p x &&& restrict p y := by
  apply bit_eq; intro i; simp only [at_bit, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero]
theorem map_or (p : Path) (x y : Table) :
    restrict p (x ||| y) = restrict p x ||| restrict p y := by
  apply bit_eq; intro i; simp only [at_bit, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero]
theorem map_not (p : Path) (x : Table) :
    restrict p (~~~x) = ~~~restrict p x := by
  apply bit_eq; intro i; simp only [at_bit, BitVec.getLsbD_not, i.isLt, (p i).isLt, decide_true, Bool.true_and]
inductive Block (s : Table → Prop) : Table → Prop where
  | raw {x} : s x → Block s x
  | zero : Block s 0
  | one : Block s (~~~0)
  | conj {x y} : Block s x → Block s y → Block s (x &&& y)
  | disj {x y} : Block s x → Block s y → Block s (x ||| y)
theorem restrict_block (p : Path) {s : Table → Prop} {q : Trace → Prop} {x : Table}
    (h : Block s x) (src : ∀ t, s t → q (restrict p t)) : MonotoneBlock q (restrict p x) := by
  have zero : restrict p 0 = 0 := by apply bit_eq; intro i; rw [at_bit]; simp [BitVec.getLsbD]
  induction h with
  | raw h => exact .raw (src _ h)
  | zero => rw [zero]; exact .zero
  | one => rw [map_not,zero]; exact .one
  | conj _ _ a b => rw [map_and]; exact .conj a b
  | disj _ _ a b => rw [map_or]; exact .disj a b

def inputs : List Table := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]
def target : Table := 36240869367020798
def paths : List Path := [![0, 1, 9, 11, 27, 31, 63],
  ![0, 1, 9, 11, 43, 47, 63],
  ![0, 1, 9, 13, 45, 47, 63],
  ![0, 1, 17, 19, 27, 31, 63],
  ![0, 1, 17, 19, 51, 55, 63],
  ![0, 1, 17, 21, 53, 55, 63],
  ![0, 1, 33, 37, 45, 47, 63],
  ![0, 1, 33, 37, 53, 55, 63],
  ![0, 2, 18, 19, 27, 31, 63],
  ![0, 2, 18, 19, 51, 55, 63],
  ![0, 2, 18, 22, 54, 55, 63],
  ![0, 2, 34, 38, 54, 55, 63],
  ![0, 4, 36, 37, 45, 47, 63],
  ![0, 4, 36, 37, 53, 55, 63],
  ![0, 4, 36, 38, 54, 55, 63]]
theorem checked_paths (p : Path) (hp : p ∈ paths) :
    (∀ x ∈ inputs, Ascending (restrict p x)) ∧ restrict p target = 42 := by
  have ht : paths.all (fun t =>
    inputs.all (fun v => falls (restrict t v) == 0) && (restrict t target == 42)) = true := by decide
  simpa [List.all_eq_true, Ascending] using List.all_eq_true.mp ht p hp

theorem both_patterns {a b : Table}
    (h₁ : Block (· ∈ inputs) a)
    (h₂ : Block (fun v => v ∈ inputs ∨ v = ~~~a) b)
    (hf : Block (fun v => v ∈ inputs ∨ v = ~~~a ∨ v = ~~~b) target)
    (p : Path) (hp : p ∈ paths) : restrict p a = 112 ∧ restrict p b = 76 := by
  obtain ⟨hs,hc⟩ := checked_paths p hp
  apply two_inverters
  · exact restrict_block p h₁ hs
  · apply restrict_block p h₂; rintro t (ht | rfl)
    · exact Or.inl (hs _ ht)
    · exact Or.inr (map_not _ _)
  · rw [← hc]
    apply restrict_block p hf
    rintro t (ht | rfl | rfl)
    · exact Or.inl (hs _ ht)
    · exact Or.inr (Or.inl (map_not _ _))
    · exact Or.inr (Or.inr (map_not _ _))

#print axioms checked_paths
#print axioms both_patterns
end Comparator9929.Paths

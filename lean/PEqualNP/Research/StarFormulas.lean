import PEqualNP.Research.FormulaTrace
import PEqualNP.Research.L_meta_1980_cap_boundary

namespace PEqualNP.Research.StarFormulas
open Finset PEqualNP.Research.FormulaTrace PEqualNP.Research.CapBoundary
abbrev Input := Fin 26
abbrev Form := Formula Input

def point (i : V) : Input := Fin.castAdd 13 i
def line (i : V) : Input := Fin.natAdd 13 i
def first (dual : Bool) := if dual then line else point
def second (dual : Bool) := if dual then point else line
def adj (dual : Bool) (i j : V) := if dual then decide (inc j i) else decide (inc i j)

def block (dual : Bool) (a b i : V) : Form :=
  let center := if i=a then Formula.join (.atom (first dual a)) (.atom (first dual b)) else .atom (first dual i)
  let joined := (List.finRange 13).filter fun j => adj dual i j || (decide (i=a) && adj dual b j)
  .meet center (disjunction (joined.map fun j => Formula.atom (second dual j)))

def merged (dual : Bool) (a b : V) : Form :=
  disjunction (((List.finRange 13).filter fun i => decide (i≠b)).map (block dual a b))

def edge (dual : Bool) (x : Input → Bool) := ∃ i j : V,
  x (first dual i)=true ∧ x (second dual j)=true ∧ adj dual i j=true
def cross (dual : Bool) (x : Input → Bool) (a b : V) :=
  (x (first dual a)=true ∨ x (first dual b)=true) ∧
    ∃ j : V,x (second dual j)=true ∧ (adj dual a j=true ∨ adj dual b j=true)

theorem block_spec (dual a b i) (x : Input → Bool) :
    truth x (block dual a b i)=true ↔
    ((if i=a then x (first dual a) || x (first dual b) else x (first dual i))=true ∧
      ∃ j : V, (adj dual i j=true ∨ i=a ∧ adj dual b j=true) ∧ x (second dual j)=true) := by
  by_cases h : i=a <;> simp [block,truth,truth_or,h,List.mem_finRange]

theorem merged_spec (dual a b) (ne : a≠b) (x : Input → Bool) :
    truth x (merged dual a b)=true ↔ edge dual x ∨ cross dual x a b := by
  simp only [merged,truth_or,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq,exists_exists_and_eq_and,block_spec]
  constructor
  · rintro ⟨i,hi,center,j,ej,hj⟩
    by_cases h : i=a
    · subst i;right
      exact ⟨by simpa using center,j,hj,ej.imp id (fun z => z.2)⟩
    · left
      exact ⟨i,j,by simpa [h] using center,hj,ej.elim id (fun e => False.elim (h e.1))⟩
  · rintro (⟨i,j,xi,xj,ij⟩|⟨cen,j,xj,ej⟩)
    · by_cases h : i=b
      · subst i
        exact ⟨a,ne,by simp [xi],j,Or.inr ⟨rfl,ij⟩,xj⟩
      · exact ⟨i,h,by split <;> simp_all,j,Or.inl ij,xj⟩
    · exact ⟨a,ne,by simpa using cen,j,ej.imp_right (fun h => ⟨rfl,h⟩),xj⟩

theorem merged_cost : ∀ dual a b, a≠b → gates (merged dual a b)=63 := by decide +kernel

end PEqualNP.Research.StarFormulas

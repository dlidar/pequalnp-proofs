import PEqualNP.Research.NecessarySamples

namespace PEqualNP.Research.FlagSamples
open PEqualNP.Research.CapBoundary PEqualNP.Research.FormulaTrace
open PEqualNP.Research.StarFormulas PEqualNP.Research.NecessarySamples

def minusFlag (a b : V) : Form :=
  disjunction ((List.finRange 13).map fun i =>
    Formula.meet (Formula.atom (point i)) (disjunction (((List.finRange 13).filter
      (fun j => decide (inc i j ∧ (i≠a ∨ j≠b)))).map fun j => Formula.atom (line j))))

theorem minus_cost : ∀ a b,inc a b → gates (minusFlag a b)=63 := by decide +kernel

theorem minus_spec (x : Word) (a b : V) :
    truth (bits x) (minusFlag a b)=true ↔
      ∃ p∈pts x,∃ l∈lines x,inc p l ∧ (p≠a ∨ l≠b) := by
  simp [minusFlag,truth_or,truth,bits_point,bits_line,List.mem_finRange]
  aesop

def flag (x : Word) := ∃ p l, inc p l ∧ pts x={p} ∧ lines x={l}

theorem demands_flags {α} (data : α → Word) (labels : Set α) (h : hard data labels)
    (yes : ∀ k∈labels,flag (data k)) (no : ∀ k∉labels,Generic (data k)) (a b : V) (adj : inc a b) :
    ∃ k∈labels,pts (data k)={a} ∧ lines (data k)={b} := by
  classical
  by_contra! miss
  apply excludes h (minusFlag a b) (minus_cost a b adj).le
  intro k
  rw [minus_spec]
  constructor
  · intro hk
    obtain ⟨p,l,pl,P,L⟩ := yes k hk
    refine ⟨p,by simp [P],l,by simp [L],pl,?_⟩
    by_contra! both
    obtain ⟨rfl,rfl⟩ := both
    exact miss k hk P L
  · rintro ⟨p,hp,l,hl,pl,_⟩
    by_contra hn
    exact (no k hn).1 p hp l hl pl

theorem flag_count : (Finset.univ.filter (fun e : V × V => inc e.1 e.2)).card=52 := by decide +kernel

end PEqualNP.Research.FlagSamples

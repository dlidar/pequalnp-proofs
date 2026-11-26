import PEqualNP.Research.NecessarySamples

namespace PEqualNP.Research.SixRowCircuit
open PEqualNP.Research.CapBoundary PEqualNP.Research.FormulaTrace PEqualNP.Research.StarFormulas
open PEqualNP.Research.StarDesign PEqualNP.Research.NecessarySamples

def separator : Form := disjunction [
  disjunction [.atom 0],
  Formula.meet (disjunction [.atom 1, .atom 3]) (disjunction [.atom 13, .atom 18]),
  Formula.meet (disjunction [.atom 6]) (disjunction [.atom 19, .atom 23]),
  Formula.meet (disjunction [.atom 3, .atom 5, .atom 6, .atom 8]) (disjunction [.atom 15, .atom 18, .atom 20]),
  Formula.meet (disjunction [.atom 5, .atom 9]) (disjunction [.atom 13, .atom 17, .atom 22]),
  Formula.meet (disjunction [.atom 2, .atom 4, .atom 7, .atom 9]) (disjunction [.atom 14, .atom 17, .atom 19, .atom 21]),
  Formula.meet (disjunction [.atom 2, .atom 8, .atom 11]) (disjunction [.atom 15, .atom 21, .atom 25]),
  Formula.meet (disjunction [.atom 7, .atom 10, .atom 11]) (disjunction [.atom 20, .atom 23, .atom 24]),
  Formula.meet (disjunction [.atom 12]) (disjunction [.atom 25]),
  disjunction [.atom 16],
  Formula.meet (disjunction [.atom 1, .atom 10, .atom 12]) (disjunction [.atom 14, .atom 22, .atom 24])]

theorem size : gates separator=48 := by decide +kernel

def flagBits (p l : V) (i : Input) := decide (i=point p ∨ i=line l)

theorem positive : ∀ p l,inc p l → truth (flagBits p l) separator=true := by decide +kernel

theorem negative : ∀ x∈design,truth (bits x) separator=false := by
  have all : design.all (fun x => !(truth (bits x) separator))=true := by decide +kernel
  intro x hx; simpa using List.all_eq_true.mp all x hx

end PEqualNP.Research.SixRowCircuit

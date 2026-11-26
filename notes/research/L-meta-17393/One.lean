import BoundTree
import Circuit
namespace PEqualNP.Research.Triangle17393.One
open Finset PEqualNP.Research.TripleFormulaMass PEqualNP.Research.BoundTree17393
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
def row (r : Fin 17) := (#[19,37,73,134,135,176,177,266,267,336,337,524,525,608,609,896,897] : Array Nat)[r.val]!
def col (c : Fin 16) := (#[126,412,413,482,483,492,682,683,724,725,730,822,824,825,838,839] : Array Nat)[c.val]!
def wt (r : Fin 17) (c : Fin 16) := (#[0,0,0,0,0,-54,0,42,0,42,41,41,0,42,0,42,0,0,42,0,42,41,0,0,0,0,-54,41,0,42,0,42,0,0,42,0,42,41,0,42,0,42,41,-54,0,0,0,0,42,0,0,15,12,42,0,0,15,12,42,0,-15,-27,15,12,0,0,0,0,15,0,0,0,0,15,0,0,0,-15,0,15,42,15,12,0,0,42,15,12,0,0,42,0,15,12,-15,-27,0,0,15,0,0,0,0,15,0,0,0,0,0,15,0,-15,42,0,0,15,12,42,15,12,-15,-27,0,42,15,12,0,0,0,0,0,0,15,0,0,15,0,-15,0,0,0,15,0,0,42,15,12,0,0,42,-15,-27,15,12,0,42,0,0,15,12,0,0,15,0,0,0,0,-15,0,15,0,0,0,0,0,15,42,15,12,-15,-27,0,0,0,15,12,42,42,15,12,0,0,0,0,15,0,-15,0,0,0,0,15,0,0,0,15,0,0,42,-15,-27,15,12,0,15,12,0,0,42,42,0,0,15,12,0,0,-15,0,15,0,0,15,0,0,0,0,0,0,0,15,-24,12,0,12,0,0,12,0,12,0,0,0,12,0,12,0,-30,0,30,0,30,0,0,30,0,30,0,0,0,30,0,30] : Array Int)[r.val*16+c.val]!
def lift (x : Fin 10 → Bool) (i : Fin 11) := if h : i.val<10 then x ⟨i.val,h⟩ else !x 0
def p (r : Fin 17) := lift (fun i => (row r).testBit i.val)
def q (c : Fin 16) := lift (fun i => (col c).testBit i.val)
def rows (i : Fin 11) := univ.filter (fun r => p r i=true)
def cols (i : Fin 11) := univ.filter (fun c => q c i=false)
theorem pos : ∀ r,triangle (fun i => (row r).testBit i.val)=true := by decide +kernel
theorem neg : ∀ c,triangle (fun i => (col c).testBit i.val)=false := by decide +kernel
theorem total : mass wt univ univ=1956 := by decide +kernel
end PEqualNP.Research.Triangle17393.One

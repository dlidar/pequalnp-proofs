import BoundTree
import Circuit
namespace PEqualNP.Research.Triangle17393.Adjacent
open Finset PEqualNP.Research.TripleFormulaMass PEqualNP.Research.BoundTree17393
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
def row (r : Fin 19) := (#[19,37,39,73,75,134,135,176,179,266,267,336,339,524,527,608,611,896,899] : Array Nat)[r.val]!
def col (c : Fin 19) := (#[124,126,412,413,480,483,492,680,683,724,725,728,730,820,822,824,825,836,839] : Array Nat)[c.val]!
def wt (r : Fin 19) (c : Fin 19) := (#[8,40,8,40,0,104,-654,0,602,0,598,0,598,0,598,0,598,0,602,0,-64,0,650,0,186,654,0,0,0,0,-468,-186,468,-186,0,654,0,468,0,64,0,0,0,436,0,0,0,0,0,0,-436,0,372,0,0,0,158,0,-64,0,650,0,186,654,0,468,0,654,468,-186,-468,-186,0,0,0,0,0,64,0,0,0,436,0,0,158,0,0,0,372,0,-436,0,0,0,0,0,650,0,-64,0,186,654,0,0,468,-186,0,654,0,0,-468,-186,0,468,0,0,0,64,0,436,0,0,0,0,372,0,0,0,0,0,-436,0,158,634,0,634,0,0,-52,654,303,351,0,0,492,182,0,0,492,182,-303,-626,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,650,0,-64,0,186,654,0,468,-468,-186,0,0,0,654,468,-186,0,0,0,0,0,64,0,436,0,0,158,0,-436,0,0,0,0,0,372,0,0,634,0,634,0,0,-52,654,-303,-626,492,182,0,0,492,182,0,0,303,351,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,634,20,634,20,0,-622,-40,0,0,468,186,468,186,468,186,468,186,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,350,284,-634,-40,0,268,60,303,-263,0,0,500,134,500,134,0,0,303,-263,-8,24,-8,-610,0,347,-24,0,642,0,0,-32,24,-32,24,0,0,0,642,-634,-40,350,284,0,268,60,303,-263,500,134,0,0,0,0,500,134,303,-263,-8,-610,-8,24,0,347,-24,0,642,-32,24,0,0,0,0,-32,24,0,642] : Array Int)[r.val*19+c.val]!
def lift (x : Fin 10 → Bool) (i : Fin 12) := if h : i.val<10 then x ⟨i.val,h⟩ else if i.val=10 then !x 0 else !x 1
def p (r : Fin 19) := lift (fun i => (row r).testBit i.val)
def q (c : Fin 19) := lift (fun i => (col c).testBit i.val)
def rows (i : Fin 12) := univ.filter (fun r => p r i=true)
def cols (i : Fin 12) := univ.filter (fun c => q c i=false)
theorem pos : ∀ r,triangle (fun i => (row r).testBit i.val)=true := by decide +kernel
theorem neg : ∀ c,triangle (fun i => (col c).testBit i.val)=false := by decide +kernel
theorem total : mass wt univ univ=28620 := by decide +kernel
end PEqualNP.Research.Triangle17393.Adjacent

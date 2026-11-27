import Mathlib
import PEqualNP.Library.Helpers.PromiseColTree

namespace PEqualNP.Research.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.Replay PEqualNP.Library.Helpers.PromiseColTree
open PEqualNP.Represents

def firstInternalNot : ℕ → List Gate → Option ℕ
  | _, [] => none
  | wire, g :: gs =>
    match g.op, g.inputs with
    | .not, a :: _ => if 64 ≤ a ∧ a < wire then some wire else firstInternalNot (wire + 1) gs
    | _, _ => firstInternalNot (wire + 1) gs

def maskOnSix (C : Circuit) : Option ℕ := do
  let w ← firstInternalNot 64 C.gates
  let col := (tcols 10 8 C 32 32).1.rd 8 w
  return ((List.range 6).filter (fun k => col.testBit (33 * k))).foldl (fun r k => r + 2^k) 0

def targetRows : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x41402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0xb01458, 0xf447af40, 0xb07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]
def actualRows : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x41402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0xb01458, 0xf447af40, 0xb07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

def codes : List (ℕ × ℕ × ℕ) := [
    (1,19,31),(1,17,45),(1,64,65),(1,0,61),(1,47,54),(1,67,68),(1,66,69),(1,18,38),
    (1,12,55),(1,71,72),(1,44,52),(1,73,74),(1,28,36),(1,52,76),(1,75,77),(1,6,10),
    (1,53,79),(1,78,80),(0,70,81),(1,10,20),(1,57,83),(1,29,35),(1,84,85),(1,13,33),
    (1,86,87),(1,15,28),(1,50,89),(1,41,90),(1,4,61),(1,9,39),(1,92,93),(1,91,94),
    (0,88,95),(1,82,96),(1,0,56),(1,76,98),(1,16,60),(1,99,100),(1,85,101),(1,57,92),
    (1,3,26),(1,103,104),(1,1,42),(1,55,106),(1,105,107),(0,102,108),(1,97,109),(1,1,28),
    (1,46,111),(1,5,20),(1,54,113),(1,112,114),(1,4,58),(1,25,43),(1,21,117),(1,116,118),
    (1,115,119),(1,79,93),(1,2,51),(1,121,122),(1,15,36),(1,3,41),(1,124,125),(1,123,126),
    (0,120,127),(1,110,128),(1,14,32),(1,45,130),(1,21,48),(1,131,132),(1,79,118),(1,10,23),
    (2,135,135),(0,134,136),(1,133,137),(1,24,34),(1,8,40),(1,139,140),(1,107,141),(0,138,142),
    (1,129,143),(1,14,39),(1,80,145),(1,0,62),(1,34,147),(1,146,148),(1,22,37),(1,100,150),
    (1,26,32),(1,151,152),(1,140,153),(0,149,154),(1,144,155),(1,13,27),(1,2,18),(1,157,158),
    (1,48,68),(1,38,160),(0,159,161),(1,156,162),(1,31,59),(1,72,164),(1,94,165),(1,77,114),
    (1,24,27),(1,60,168),(1,167,169),(0,166,170),(1,163,171),(1,14,116),(1,19,52),(1,173,174),
    (1,87,175),(1,11,53),(1,152,177),(1,126,178),(0,176,179),(1,172,180),(1,62,140),(1,74,182),
    (1,30,46),(1,40,184),(1,11,185),(1,183,186),(1,69,134),(0,187,188),(1,181,189),(1,45,63),
    (1,122,191),(1,135,192),(1,33,47),(1,58,194),(1,93,195),(1,113,196),(1,147,197),(0,193,198),
    (1,190,199),(1,9,85),(1,158,201),(1,160,202),(1,49,63),(1,119,204),(0,203,205),(1,200,206),
    (1,24,65),(1,186,208),(1,42,174),(1,35,124),(1,25,211),(1,210,212),(0,209,213),(1,207,214),
    (1,26,50),(1,132,216),(1,169,217),(1,18,37),(1,47,219),(1,135,220),(1,212,221),(0,218,222),
    (1,215,223),(1,9,51),(1,59,225),(1,24,52),(1,226,227),(1,219,228),(1,4,42),(1,16,230),
    (1,125,231),(1,182,232),(0,229,233),(1,224,234),(1,7,22),(1,59,236),(1,117,237),(1,148,238),
    (1,44,106),(1,87,240),(1,90,241),(0,239,242),(1,235,243)]

def circuit : Circuit :=
  ⟨codes.map (fun (o,a,b) => if o = 2 then ⟨.not, [a]⟩ else ⟨if o = 0 then .and else .or, [a,b]⟩), 244⟩

theorem checkedShape : FanInTwo circuit ∧ circuit.size = 181 ∧ maskOnSix circuit = some 63 := by
  refine ⟨fanInTwoB_sound ?_, ?_, ?_⟩ <;> decide +kernel

theorem checkedFunction : Represents (fun (u v : Fin 32) => (actualRows.getD u.val 0).testBit v.val) circuit := by
  apply represents_of_tcols (N := 10) (D := 8) (by decide) circuit
  · intro r hr
    simp only [actualRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel

def extras (left right : List ℕ) : ℕ :=
  ((List.range 32).map (fun u =>
    ((List.range 32).filter (fun v => (left.getD u 0).testBit v && !(right.getD u 0).testBit v)).length)).sum

theorem checkedErrors : extras actualRows targetRows = 0 ∧ extras targetRows actualRows = 0 := by
  decide +kernel

end PEqualNP.Research.OneNot

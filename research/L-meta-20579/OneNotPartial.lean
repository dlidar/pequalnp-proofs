import Mathlib
import PEqualNP.Library.Helpers.PromiseColTree

namespace PEqualNP.Research.OneNotPartial

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
def actualRows : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x41402, 0x6869a8a5, 0xd6586f1a, 0x7455f9a3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6aa804a4, 0xb01458, 0xf447af40, 0xb07351, 0xa8882290, 0x40d9d79c, 0x40241486, 0x50050082, 0x68812fb9, 0x50ddf79e, 0x5530009e, 0x28c180f8, 0x6ac8ae9e, 0xa6860c80, 0x20508c18, 0x10f01050]

def codes : List (ℕ × ℕ × ℕ) := [
    (1,19,31),(1,17,45),(1,64,65),(1,0,61),(1,47,54),(1,67,68),(1,66,69),(1,18,38),
    (1,12,55),(1,71,72),(1,44,52),(1,73,74),(1,28,36),(1,52,76),(1,75,77),(1,6,10),
    (1,53,79),(1,78,80),(0,70,81),(1,29,35),(1,57,83),(1,13,33),(1,84,85),(1,15,28),
    (1,50,87),(1,4,61),(1,9,39),(1,89,90),(1,88,91),(0,86,92),(1,82,93),(1,0,56),
    (1,76,95),(1,16,60),(1,96,97),(1,83,98),(1,57,89),(1,3,26),(1,100,101),(1,1,42),
    (1,55,103),(1,102,104),(0,99,105),(1,94,106),(1,1,28),(1,46,108),(1,5,20),(1,54,110),
    (1,109,111),(1,4,58),(1,25,43),(1,21,114),(1,113,115),(1,112,116),(1,79,90),(1,2,51),
    (1,118,119),(1,15,36),(1,3,41),(1,121,122),(1,120,123),(0,117,124),(1,107,125),(1,14,32),
    (1,45,127),(1,48,128),(1,79,115),(1,10,23),(2,131,131),(0,130,132),(1,129,133),(1,24,34),
    (1,8,40),(1,135,136),(1,104,137),(0,134,138),(1,126,139),(1,14,39),(1,80,141),(1,0,62),
    (1,34,143),(1,142,144),(1,22,37),(1,97,146),(1,26,32),(1,147,148),(1,136,149),(0,145,150),
    (1,140,151),(1,13,27),(1,2,18),(1,153,154),(1,48,68),(1,38,156),(0,155,157),(1,152,158),
    (1,31,59),(1,72,160),(1,91,161),(1,77,111),(1,24,27),(1,60,164),(1,163,165),(0,162,166),
    (1,159,167),(1,14,113),(1,19,52),(1,169,170),(1,85,171),(1,11,53),(1,148,173),(1,123,174),
    (0,172,175),(1,168,176),(1,62,136),(1,74,178),(1,30,46),(1,40,180),(1,11,181),(1,179,182),
    (1,69,130),(0,183,184),(1,177,185),(1,45,63),(1,119,187),(1,131,188),(1,33,90),(1,110,190),
    (1,143,191),(0,189,192),(1,186,193),(1,83,154),(1,156,195),(1,49,63),(1,116,197),(0,196,198),
    (1,194,199),(1,65,182),(1,42,170),(1,35,121),(1,25,203),(1,202,204),(0,201,205),(1,200,206),
    (1,48,50),(1,165,208),(1,18,37),(1,131,210),(1,204,211),(0,209,212),(1,207,213),(1,9,51),
    (1,59,215),(1,24,216),(1,210,217),(1,4,42),(1,16,219),(1,122,220),(1,178,221),(0,218,222),
    (1,214,223),(1,7,22),(1,59,225),(1,114,226),(1,144,227),(1,44,103),(1,85,229),(1,88,230),
    (0,228,231),(1,224,232)]

def circuit : Circuit :=
  ⟨codes.map (fun (o,a,b) => if o = 2 then ⟨.not, [a]⟩ else ⟨if o = 0 then .and else .or, [a,b]⟩), 233⟩

theorem checkedShape : FanInTwo circuit ∧ circuit.size = 170 ∧ maskOnSix circuit = some 63 := by
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

theorem checkedErrors : extras actualRows targetRows = 0 ∧ extras targetRows actualRows = 13 := by
  decide +kernel

end PEqualNP.Research.OneNotPartial

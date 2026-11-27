import Coverage
import PEqualNP.Library.Helpers.Replay
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def ref19 : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.and,[5,8]⟩, ⟨.and,[4,8]⟩, ⟨.and,[5,7]⟩, ⟨.or,[11,12]⟩, ⟨.and,[0,13]⟩, ⟨.and,[3,8]⟩, ⟨.and,[5,6]⟩, ⟨.or,[15,16]⟩, ⟨.and,[1,17]⟩, ⟨.and,[3,7]⟩, ⟨.and,[4,6]⟩, ⟨.or,[19,20]⟩, ⟨.and,[2,21]⟩, ⟨.and,[9,10]⟩, ⟨.and,[6,23]⟩, ⟨.or,[14,24]⟩, ⟨.or,[22,25]⟩, ⟨.or,[18,26]⟩],27⟩
def drow (j k : ℕ) : Fin 512 := ([1, 2, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 3, 272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 160, 3, 160, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 160, 3, 160, 160, 272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 161, 3, 161, 161, 160, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 3, 264, 264, 160, 160, 161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 96, 96, 3, 96, 96, 96, 96, 96, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 96, 96, 3, 96, 96, 96, 96, 96, 96, 264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 98, 98, 3, 98, 98, 98, 98, 98, 98, 96, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 136, 3, 136, 136, 136, 136, 136, 136, 96, 96, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 80, 80, 3, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 80, 80, 3, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 136, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 84, 84, 3, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 80, 80, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 3, 288, 272, 160, 160, 161, 264, 96, 96, 98, 136, 80, 80, 84, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 3, 288, 272, 160, 160, 161, 264, 96, 96, 98, 136, 80, 80, 84, 291, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 161, 3, 161, 161, 160, 160, 355, 161, 96, 96, 98, 136, 80, 80, 84, 161, 161, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 84, 84, 3, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 80, 80, 161, 84, 84, 84, 0, 0, 1, 2, 4, 8, 16, 32, 64, 84, 84, 3, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 80, 80, 98, 84, 84, 84, 98, 0] : List (Fin 512)).getD (28*j+k) 0
def onrow (j : ℕ) : Fin 512 := ([3, 288, 272, 160, 160, 161, 264, 96, 96, 98, 136, 80, 80, 84, 291, 355, 161, 84, 84] : List (Fin 512)).getD j 0
def offrow (j : ℕ) : Fin 512 := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List (Fin 512)).getD j 0
def value (w : ℕ) (r : Fin 512) := (ref19.wires (List.ofFn (px r))).getD w false
theorem nonconstant19 : ∀ j : Fin 19, value (9+j.val) (onrow j) ≠ value (9+j.val) (offrow j) := by decide +kernel
theorem distinct19 : ∀ (j : Fin 19) (k : Fin 28), k.val < 9+j.val → value (9+j.val) (drow j k) ≠ value k.val (drow j k) := by decide +kernel
theorem nineteen : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 19 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩ := by
  refine ⟨ref19,PEqualNP.Library.Helpers.Replay.fanInTwoB_sound (by decide +kernel),rfl,?_,rfl,?_,?_,?_,rfl,rfl⟩
  · decide +kernel
  · intro j
    fin_cases j <;> right <;> first | exact ⟨Or.inl rfl,_,_,by decide,by decide,rfl⟩ | exact ⟨Or.inr rfl,_,_,by decide,by decide,rfl⟩
  · intro j
    let i : Fin 19 := j
    refine ⟨⟨px (onrow i),px (offrow i),nonconstant19 i⟩,?_⟩
    intro k hk
    let t : Fin 28 := ⟨k,by have := i.isLt; change k < 9+i.val at hk; omega⟩
    exact ⟨px (drow i t),distinct19 i t hk⟩
  · decide +kernel
#print axioms nineteen
end PEqualNP.Research.Permanent27300

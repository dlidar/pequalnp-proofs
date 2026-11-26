import PEqualNP.Defs
import PEqualNP.Research.SixCofactors3321

namespace PEqualNP.Research.ReadNormalSmall
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Research.GateCuts3321 PEqualNP.Research.SixCofactors3321

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

def hits (es : List (Fin 8 × Fin 8)) (x : Fin 8 → Bool) := es.any fun e => x e.1 && x e.2

theorem pair_test (es : List (Fin 8 × Fin 8)) (C : Circuit)
    (ok : ∀ x, circuitFun 8 C x = hits es x) (k : Nat)
    (test : ∀ e ∈ es, readsAtMost C 8 (setList ({e.1,e.2} : Finset (Fin 8))) k = true) :
    IsReadK 8 C k := by
  intro S hs
  obtain ⟨yes,no⟩ := hs
  rw [ok] at yes
  obtain ⟨e,he,h⟩ := List.any_eq_true.mp yes
  have both : e.1 ∈ S ∧ e.2 ∈ S := by simpa [setInput] using h
  let T : Finset (Fin 8) := {e.1,e.2}
  have sub : T ⊆ S := by
    intro j hj
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl
    · exact both.1
    · exact both.2
  have ht : circuitFun 8 C (setInput T) = true := by
    rw [ok]; apply List.any_eq_true.mpr; exact ⟨e,he,by simp [setInput,T]⟩
  have eq : T = S := by
    by_contra ne
    have bad := no T (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne sub ne))
    simp [ht] at bad
  rw [←eq]; exact test e he

theorem ao_fan {n} {C : Circuit} (h : IsAO2 n C) : FanInTwo C := by
  intro g hg
  have op := h.1 g hg
  exact ⟨by rcases op with a|a <;> simp [a], (h.2.2 g hg).le⟩

namespace M862
def edges : List (Fin 8 × Fin 8) := [(0, 5), (0, 6), (0, 7), (1, 4), (1, 6), (2, 4), (2, 5)]
def witness : Circuit := ⟨[⟨.or,[5,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[4,6]⟩, ⟨.and,[1,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[2,13]⟩, ⟨.or,[10,12]⟩, ⟨.or,[15,14]⟩],16⟩
theorem size_eq : witness.size = 9 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph862 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
theorem normalize (C : Circuit) (legalC : IsAO2 8 C) (ev : ∀ x, circuitFun 8 C x = graph862 x) :
    ∃ D : Circuit, IsAO2 8 D ∧ (∀ x, circuitFun 8 D x = graph862 x) ∧ D.size ≤ C.size ∧ IsReadK 8 D 2 := by
  exact ⟨witness,legal,eval_eq, size_eq ▸ lower_graph862 C.size ⟨C,ao_fan legalC,le_rfl,ev⟩,read_two⟩
end M862

namespace M5804
def edges : List (Fin 8 × Fin 8) := [(0, 6), (0, 7), (1, 5), (1, 7), (2, 5), (2, 6), (3, 4)]
def witness : Circuit := ⟨[⟨.or,[6,7]⟩, ⟨.and,[0,8]⟩, ⟨.or,[5,7]⟩, ⟨.and,[1,10]⟩, ⟨.or,[5,6]⟩, ⟨.and,[2,12]⟩, ⟨.and,[3,4]⟩, ⟨.or,[9,11]⟩, ⟨.or,[15,13]⟩, ⟨.or,[16,14]⟩],17⟩
theorem size_eq : witness.size = 10 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph5804 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
theorem normalize (C : Circuit) (legalC : IsAO2 8 C) (ev : ∀ x, circuitFun 8 C x = graph5804 x) :
    ∃ D : Circuit, IsAO2 8 D ∧ (∀ x, circuitFun 8 D x = graph5804 x) ∧ D.size ≤ C.size ∧ IsReadK 8 D 2 := by
  exact ⟨witness,legal,eval_eq, size_eq ▸ lower_graph5804 C.size ⟨C,ao_fan legalC,le_rfl,ev⟩,read_two⟩
end M5804

namespace M5805
def edges : List (Fin 8 × Fin 8) := [(0, 4), (0, 6), (0, 7), (1, 5), (1, 7), (2, 5), (2, 6), (3, 4)]
def witness : Circuit := ⟨[⟨.or,[4,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[5,7]⟩, ⟨.and,[1,11]⟩, ⟨.or,[5,6]⟩, ⟨.and,[2,13]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,12]⟩, ⟨.or,[16,14]⟩, ⟨.or,[17,15]⟩],18⟩
theorem size_eq : witness.size = 11 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph5805 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
theorem normalize (C : Circuit) (legalC : IsAO2 8 C) (ev : ∀ x, circuitFun 8 C x = graph5805 x) :
    ∃ D : Circuit, IsAO2 8 D ∧ (∀ x, circuitFun 8 D x = graph5805 x) ∧ D.size ≤ C.size ∧ IsReadK 8 D 2 := by
  exact ⟨witness,legal,eval_eq, size_eq ▸ lower_graph5805 C.size ⟨C,ao_fan legalC,le_rfl,ev⟩,read_two⟩
end M5805

namespace M4958
def edges : List (Fin 8 × Fin 8) := [(0, 5), (0, 6), (0, 7), (1, 4), (1, 6), (2, 4), (2, 5), (3, 4)]
def witness : Circuit := ⟨[⟨.or,[5,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[4,6]⟩, ⟨.and,[1,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[2,13]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,12]⟩, ⟨.or,[16,14]⟩, ⟨.or,[17,15]⟩],18⟩
theorem size_eq : witness.size = 11 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph4958 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
end M4958

namespace M4973
def edges : List (Fin 8 × Fin 8) := [(0, 4), (0, 6), (0, 7), (1, 5), (1, 6), (2, 4), (2, 5), (3, 4)]
def witness : Circuit := ⟨[⟨.or,[4,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[2,13]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,12]⟩, ⟨.or,[16,14]⟩, ⟨.or,[17,15]⟩],18⟩
theorem size_eq : witness.size = 11 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph4973 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
end M4973

namespace M13726
def edges : List (Fin 8 × Fin 8) := [(0, 5), (0, 6), (0, 7), (1, 4), (1, 7), (2, 4), (2, 6), (3, 4), (3, 5)]
def witness : Circuit := ⟨[⟨.or,[5,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[4,7]⟩, ⟨.and,[1,11]⟩, ⟨.or,[4,6]⟩, ⟨.and,[2,13]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,15]⟩, ⟨.or,[10,12]⟩, ⟨.or,[17,14]⟩, ⟨.or,[18,16]⟩],19⟩
theorem size_eq : witness.size = 12 := rfl
theorem legal : IsAO2 8 witness := by decide +kernel
theorem eval_eq : ∀ x, circuitFun 8 witness x = graph13726 x := by decide +kernel
theorem read_one : IsReadK 8 witness 1 := pair_test edges witness (by decide +kernel) 1 (by decide +kernel)
theorem read_two : IsReadK 8 witness 2 := pair_test edges witness (by decide +kernel) 2 (by decide +kernel)
end M13726

end PEqualNP.Research.ReadNormalSmall

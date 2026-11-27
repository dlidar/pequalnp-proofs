import TraceCheck
import Certificate
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def binaries (ls : List Gate) := ls.countP (fun g => decide (g.inputs.length = 2))
theorem port_bound (ls : List Gate) (hl : ∀ g ∈ ls, g.inputs.length ≤ 2) :
    (ls.flatMap Gate.inputs).length ≤ ls.length + binaries ls := by
  induction ls with
  | nil => simp [binaries]
  | cons g gs ih =>
    have h := hl g (by simp)
    have tail := ih (fun g' hg => hl g' (by simp [hg]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    by_cases eq : g.inputs.length = 2 <;>
      simp [binaries,List.countP_cons,eq] at tail ⊢ <;> omega
theorem binary_perm (gs : List Gate) (o : ℕ) (sz : binaries gs ≤ 10) (out : o+1 = 11+gs.length)
    (hg : ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j))
    (live : ∀ j : Fin (first::second::gs).length, j.val+1 < (first::second::gs).length →
      ∃ k : Fin (first::second::gs).length, j.val < k.val ∧
        9+j.val ∈ ((first::second::gs).get k).inputs)
    (he : ∀ x, (Circuit.mk (first::second::gs) o).eval (List.ofFn x) = perm3 x) :
    (List.range (11+gs.length)).Perm (uses ⟨gs,o⟩) := by
  have raws := raw_coverage (backward o hg) he
  have sub : List.range (11+gs.length) ⊆ uses ⟨gs,o⟩ := by
    intro w hw
    have bound := List.mem_range.mp hw
    by_cases h : w < 9
    · exact raws ⟨w,h⟩
    by_cases last : w = o
    · simp [uses,last]
    let j : Fin (first::second::gs).length := ⟨w-9,by simp <;> omega⟩
    have hj : j.val+1 < (first::second::gs).length := by dsimp [j]; simp; omega
    obtain ⟨k,_,hk⟩ := live j hj
    have eq : 9+j.val = w := by dsimp [j]; omega
    rw [eq] at hk
    have allm : w ∈ (first::second::gs).flatMap Gate.inputs := List.mem_flatMap.mpr ⟨_,List.get_mem (first::second::gs) k,hk⟩
    simp [first,second] at allm
    apply List.mem_cons_of_mem
    rcases allm with hh|hh|hh|hh|hh <;> first | omega | exact List.mem_flatMap.mpr hh | assumption
  apply (List.subperm_of_subset List.nodup_range sub).perm_of_length_le
  have lens : ∀ g ∈ gs, g.inputs.length ≤ 2 := by
    intro g hm
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hm
    exact (legal_bounds (hg ⟨j,hj⟩)).1
  have hlen := port_bound gs lens
  change (o::gs.flatMap Gate.inputs).length ≤ (List.range (11+gs.length)).length
  rw [List.length_cons,List.length_range]
  omega
theorem ten_later_binary_impossible (gs : List Gate) (o : ℕ) (sz : binaries gs ≤ 10) (out : o+1 = 11+gs.length)
    (hg : ∀ j : Fin (first::second::gs).length, Legal (9+j.val) ((first::second::gs).get j))
    (live : ∀ j : Fin (first::second::gs).length, j.val+1 < (first::second::gs).length →
      ∃ k : Fin (first::second::gs).length, j.val < k.val ∧ 9+j.val ∈ ((first::second::gs).get k).inputs)
    (he : ∀ x, (Circuit.mk (first::second::gs) o).eval (List.ofFn x) = perm3 x) : False := by
  let D : Circuit := ⟨gs,o⟩
  have hl := tail_legal hg
  have hb := backward o hl
  have hp := binary_perm gs o sz out hl live he
  have le := output_budget (price D) 11 gs o hp (fun j => step_price combine complement hb j (hl j))
  rw [input_price] at le
  have eq : values D o = fun t => perm3 (cut t) := funext fun t => he (cut t)
  have five : measuredCost (signature fun t => perm3 (cut t)) = 5 := by decide +kernel
  simp [price,eq,five] at le
theorem thirteen_binary (gs : List Gate) (o : ℕ) (out : o+1 = 11+gs.length)
    (hg : ∀ j : Fin (first::second::gs).length, Legal (9+j.val) ((first::second::gs).get j))
    (live : ∀ j : Fin (first::second::gs).length, j.val+1 < (first::second::gs).length →
      ∃ k : Fin (first::second::gs).length, j.val < k.val ∧ 9+j.val ∈ ((first::second::gs).get k).inputs)
    (he : ∀ x, (Circuit.mk (first::second::gs) o).eval (List.ofFn x) = perm3 x) : 13 ≤ binaries (first::second::gs) := by
  have lower : 11 ≤ binaries gs := by
    by_contra hn
    exact ten_later_binary_impossible gs o (by omega) out hg live he
  have count : binaries (first::second::gs) = binaries gs+2 := by simp [binaries,first,second,Nat.add_assoc]
  omega
#print axioms thirteen_binary
end PEqualNP.Research.Permanent27300

import Coverage
namespace PEqualNP.Research.Permanent27300
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Legal (m : ℕ) (g : Gate) := (g.op = .not ∧ ∃ a, a < m ∧ g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < m ∧ g.inputs = [a,b])

theorem legal_bounds {g : Gate} {m : ℕ} (h : Legal m g) :
    g.inputs.length ≤ 2 ∧ ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_,b,hb,e⟩ | ⟨_,a,b,hab,hb,e⟩
  · simp [e,hb]
  · simp [e,hb,hab.trans hb]

theorem tail_legal {gs : List Gate}
    (hg : ∀ j : Fin (first::second::gs).length, Legal (9+j.val) ((first::second::gs).get j)) :
    ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j) := by
  intro j
  have h := hg ⟨j.val+2, by simp <;> omega⟩
  simpa [show 9+(j.val+2) = 11+j.val by omega,List.get_eq_getElem] using h

theorem backward {gs : List Gate} (o : ℕ) (hg : ∀ j : Fin gs.length, Legal (11+j.val) (gs.get j)) :
    ReadsBack 11 (Circuit.mk gs o) := by
  intro j hj a hm
  change a ∈ (gs.getD j _).inputs at hm
  rw [List.getD_eq_getElem _ _ hj] at hm
  exact (legal_bounds (hg ⟨j,hj⟩)).2 _ hm

theorem wire_perm (gs : List Gate) (o : ℕ) (sz : gs.length ≤ 10) (out : o+1 = 11+gs.length)
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
  have le : ∀ ls : List Gate, (∀ g ∈ ls, g.inputs.length ≤ 2) →
      (ls.flatMap Gate.inputs).length ≤ 2*ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons g gs ih =>
      intro H
      have := H g (by simp)
      have := ih fun g' hg' => H g' (by simp [hg'])
      simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega
  have hlen := le gs lens
  change (o::gs.flatMap Gate.inputs).length ≤ (List.range (11+gs.length)).length
  rw [List.length_cons,List.length_range]
  omega
end PEqualNP.Research.Permanent27300

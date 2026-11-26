import PEqualNP.Research.Cached3803.PackingChild
import PEqualNP.Research.Cached3803.GeometryChild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.Research.SelectorBound PEqualNP.Research.FlagGeometry3803
namespace PEqualNP.Research.CachedClauses3803
def clause (s : List ℕ) (x : List Bool) := s.any (fun i => x.getD i false)
def cache (s : List ℕ) (x : List Bool) := x ++ [clause s x]
theorem clause_agree (s : List ℕ) (x y z : List Bool) (h : agree false x y z) :
    clause s x = false → clause s y = false → clause s z = false := by
  simp only [clause,List.any_eq_false]
  intro hx hy i hi
  have hn := h i (by simpa [SelectorBound.read] using hx i hi) (by simpa [SelectorBound.read] using hy i hi)
  simpa [SelectorBound.read] using hn
theorem neg_pack (s : List ℕ) (i j : Fin 234) (lt : i < j) :
    ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      agree false (cache s (negRow i)) (cache s (negRow j)) (cache s (incidenceInput {p} {l})) := by
  obtain ⟨p,l,inc,h⟩ := negative_join i j lt
  exact ⟨p,l,inc,append_agree (by simp [negRow,incidenceInput]) (by simp [negRow,incidenceInput]) h (clause_agree s _ _ _ h)⟩
theorem and_count (s : List ℕ) (C : Circuit) (h : Monotone2 C)
    (pos : ∀ l p, p ∈ singerLines3 l → C.eval (cache s (incidenceInput {p} {l})) = true)
    (neg : ∀ Q, IsQuadrangle singerLines3 Q → C.eval (cache s (incidenceInput Q (missLines singerLines3 Q))) = false) :
    8 ≤ total false C.gates := by
  have bound := circuit_packing false C h (fun i => cache s (negRow i)) (fun i => neg _ (point_ok i)) (by
    intro i j lt
    obtain ⟨p,l,inc,h⟩ := neg_pack s i j lt
    exact ⟨_,by simp [cache,negRow,incidenceInput],by simp [cache,negRow,incidenceInput],h,by simp [pos l p inc]⟩)
  by_contra! hc
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) (show total false C.gates ≤ 7 by omega)
  omega
theorem cnf_lower {m : ℕ} (s : List ℕ) (tests : Fin m → List ℕ)
    (pos : ∀ l p, p ∈ singerLines3 l → ∀ t, clause (tests t) (cache s (incidenceInput {p} {l})) = true)
    (neg : ∀ Q, IsQuadrangle singerLines3 Q → ∃ t, clause (tests t) (cache s (incidenceInput Q (missLines singerLines3 Q))) = false) :
    234 ≤ m := by
  classical
  have hn (i : Fin 234) := neg _ (point_ok i)
  choose f hf using hn
  have sep : ∀ i j, i < j → f i ≠ f j := by
    intro i j lt eq
    obtain ⟨p,l,inc,h⟩ := neg_pack s i j lt
    have hf' : clause (tests (f i)) (cache s (negRow j)) = false := eq.symm ▸ hf j
    have bad := clause_agree (tests (f i)) _ _ _ h (hf i) hf'
    rw [pos l p inc] at bad
    contradiction
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i j with h|h|h
    · exact (sep i j h eq).elim
    · exact h
    · exact (sep j i h eq.symm).elim
  simpa using Fintype.card_le_of_injective f inj
end PEqualNP.Research.CachedClauses3803
namespace PEqualNP.Research.CachedClauses3803
theorem quad_count : (quadrangles singerLines3).card = 234 := by decide +kernel
theorem all_quads : Finset.univ.image Q = quadrangles singerLines3 := by
  have sub : Finset.univ.image Q ⊆ quadrangles singerLines3 := by
    intro s hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(point_ok i).1⟩,(point_ok i).2⟩
  have inj : Function.Injective Q := by intro i j e; exact q_strict.injective (congrArg key e)
  apply Finset.eq_of_subset_of_card_le sub
  simp [Finset.card_image_of_injective _ inj,quad_count]
private theorem readP (X Y : bits) (p : Fin 13) :
    (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
  fin_cases p <;> simp [incidenceInput]
private theorem readL (X Y : bits) (l : Fin 13) :
    (incidenceInput X Y).getD (13+l.val) false = decide (l ∈ Y) := by
  fin_cases l <;> simp [incidenceInput]
def complementClause (i : Fin 234) : List ℕ := (List.range 26).filter (fun a => !(negRow i).getD a false)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cnf_upper (s : List ℕ) :
    (∀ l p, p ∈ singerLines3 l → ∀ i, clause (complementClause i) (cache s (incidenceInput {p} {l})) = true) ∧
    (∀ T, IsQuadrangle singerLines3 T → ∃ i, clause (complementClause i) (cache s (incidenceInput T (missLines singerLines3 T))) = false) := by
  have plen (A B : bits) : (incidenceInput A B).length = 26 := by simp [incidenceInput]
  have pin (A B : bits) (a : ℕ) (ha : a < 26) : (cache s (incidenceInput A B)).getD a false = (incidenceInput A B).getD a false := by
    exact List.getD_append _ _ _ _ (by simpa only [plen] using ha)
  constructor
  · intro l p inc i
    apply List.any_eq_true.mpr
    by_cases h : p ∈ Q i
    · have miss : l ∉ missLines singerLines3 (Q i) := by
        intro hl
        exact Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2 inc h
      refine ⟨13+l.val,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,?_⟩
      · simp only [negRow,readL]; simp [miss]
      · rw [pin _ _ _ (by omega),readL]; simp
    · refine ⟨p.val,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,?_⟩
      · simp only [negRow,readP]; simp [h]
      · rw [pin _ _ _ (by omega),readP]; simp
  · intro T h
    have mem : T ∈ quadrangles singerLines3 := Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.1⟩,h.2⟩
    rw [← all_quads] at mem
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mem
    refine ⟨i,List.any_eq_false.mpr ?_⟩
    intro a ha
    obtain ⟨hr,hz⟩ := List.mem_filter.mp ha
    rw [pin _ _ _ (List.mem_range.mp hr)]
    simpa [negRow] using hz
end PEqualNP.Research.CachedClauses3803

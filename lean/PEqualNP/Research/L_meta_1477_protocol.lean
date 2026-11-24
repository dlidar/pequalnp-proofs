import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Research.planeRouting : ∀ (A B : Type) (n : ℕ) (P : A → Fin n → Bool) (N : B → Fin n → Bool) (C : Circuit), Monotone2 C → 
    let step := fun (F : Set (Set A × Set B)) (r : Set A × Set B) =>
      F ∪ {t | t=r ∧ ∃ u ∈ F, ∃ v ∈ F, t.1 ×ˢ t.2 ⊆ (u.1 ×ˢ u.2) ∪ (v.1 ×ˢ v.2)}
    let F : Set (Set A × Set B) := {(∅,Set.univ)} ∪
      Set.range (fun i : Fin n => ({a | P a i = true},{b | N b i = false}))
    (∀ a, C.eval (List.ofFn (P a)) = true) → (∀ b, C.eval (List.ofFn (N b)) = false) →
    ∃ Q : List (Set A × Set B), Q.length = C.size ∧ (Set.univ,Set.univ) ∈ Q.foldl step F := by
  intro A B n P N C hm step F pos neg
  classical
  let gate := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  let wire := fun (G : List Gate) (x : Fin n → Bool) (k : ℕ) => (G.foldl gate (List.ofFn x)).getD k false
  let rect := fun (G : List Gate) (k : ℕ) => (({a | wire G (P a) k = true} : Set A),({b | wire G (N b) k = false} : Set B))
  have lengthW (ts : List Gate) (w : List Bool) : (ts.foldl gate w).length = w.length + ts.length := by
    induction ts generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [gate]; omega
  have read {T : Type} (v : List T) (x d : T) (k : ℕ) :
      (v ++ [x]).getD k d = (if k < v.length then v.getD k d else if k=v.length then x else d) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
    split <;> rename_i h
    · rfl
    · by_cases eq : k = v.length
      · simp [eq]
      · have hlt : 1 ≤ k-v.length := by omega
        simp [eq,List.getElem?_eq_none (show [x].length ≤ k-v.length from hlt)]
  have wireStep (G : List Gate) (g : Gate) (x : Fin n → Bool) (k : ℕ) :
      wire (G++[g]) x k = if k < n+G.length then wire G x k else if k=n+G.length then g.op.eval (g.inputs.map (wire G x)) else false := by
    simp only [wire,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [show gate (List.foldl gate (List.ofFn x) G) g = _ ++ [_] from rfl,read,lengthW,List.length_ofFn]
  have sim (G : List Gate) (valid : ∀ g ∈ G, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      ∃ Q : List (Set A × Set B), Q.length = G.length ∧ ∀ k, rect G k ∈ Q.foldl step F := by
    induction G using List.reverseRecOn with
    | nil =>
      refine ⟨[],rfl,?_⟩
      intro k
      by_cases h : k < n
      · apply Or.inr
        exact ⟨⟨k,h⟩,by simp [rect,wire,List.getD_eq_getElem?_getD,h]⟩
      · apply Or.inl
        simp [rect,wire,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn _).length ≤ k)]
    | append_singleton gs g ih =>
      obtain ⟨Q,len,inv⟩ := ih (fun t ht => valid t (by simp [ht]))
      obtain ⟨op,arity⟩ := valid g (by simp)
      let r := rect (gs++[g]) (n+gs.length)
      refine ⟨Q ++ [r],by simp [len],?_⟩
      intro k
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
      by_cases eq : k = n+gs.length
      · subst k
        apply Or.inr
        refine ⟨rfl,_,inv (g.inputs.getD 0 0),_,inv (g.inputs.getD 1 (g.inputs.getD 0 0)),?_⟩
        rintro ⟨a,b⟩ ⟨hp,hn⟩
        change wire (gs++[g]) (P a) _ = true at hp
        change wire (gs++[g]) (N b) _ = false at hn
        simp only [wireStep,lt_self_iff_false,ite_false,ite_true] at hp hn
        change (_ ∧ _) ∨ (_ ∧ _)
        change (wire gs (P a) _ = true ∧ wire gs (N b) _ = false) ∨ (wire gs (P a) _ = true ∧ wire gs (N b) _ = false)
        rcases h : g.inputs with _|⟨i,_|⟨t,ts⟩⟩
        all_goals try have hts : ts = [] := List.eq_nil_of_length_eq_zero (by simp [h] at arity; omega)
        all_goals first | subst ts | skip
        all_goals rcases op with op|op
        all_goals simp_all [GateOp.eval,Bool.and_eq_true,Bool.or_eq_true] <;> grind
      · apply Or.inl
        have same (x : Fin n → Bool) : wire (gs++[g]) x k = wire gs x k := by
          rw [wireStep]
          split
          · rfl
          · simp [eq,wire,List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (gs.foldl gate (List.ofFn x)).length ≤ k by rw [lengthW,List.length_ofFn]; omega)]
        simpa only [rect,same] using inv k
  obtain ⟨Q,len,inv⟩ := sim C.gates (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩)
  have hp (a) : wire C.gates (P a) C.output = true := pos a
  have hn (b) : wire C.gates (N b) C.output = false := neg b
  exact ⟨Q,len,by simpa [rect,hp,hn] using inv C.output⟩

-- Each nonempty rectangle covered by two predecessors admits an AND or OR merge.
-- A rectangle already carried by one predecessor can use a copy gate.
theorem PEqualNP.Research.twoRectangleMerge {A B : Type} (I U V : Set A) (J S T : Set B)
    (h : I ×ˢ J ⊆ (U ×ˢ S) ∪ (V ×ˢ T)) (hi : I.Nonempty) (hj : J.Nonempty) :
    (I ⊆ U ∧ J ⊆ S) ∨ (I ⊆ V ∧ J ⊆ T) ∨
    (I ⊆ U ∩ V ∧ J ⊆ S ∪ T) ∨ (I ⊆ U ∪ V ∧ J ⊆ S ∩ T) := by
  classical
  have cov (a) (ha : a ∈ I) (b) (hb : b ∈ J) :
      (a ∈ U ∧ b ∈ S) ∨ (a ∈ V ∧ b ∈ T) := h (show (a,b) ∈ I ×ˢ J from ⟨ha,hb⟩)
  obtain ⟨a,ha⟩ := hi
  obtain ⟨b,hb⟩ := hj
  simp only [Set.subset_def,Set.mem_inter_iff,Set.mem_union] at ⊢
  grind

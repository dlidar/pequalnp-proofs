import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm Finset

-- Charge surplus peripheral edges to distinct pairs of matched endpoints.
-- Only maximum matchings with fourth power exceeding the input scale remain.
theorem PEqualNP.Outside.R_meta_4960_619
  (periphery : ∀ (p l : ℕ) (E M : Finset (Fin p × Fin l)), (∀ a c b d, a ≠ c → b ≠ d → ¬ ((a,b) ∈ E ∧ (a,d) ∈ E ∧ (c,b) ∈ E ∧ (c,d) ∈ E)) → (∀ e ∈ E, e.1 ∈ M.image Prod.fst ∨ e.2 ∈ M.image Prod.snd) →
    E.card + M.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card + 2*M.card^2)
  (support : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ x, circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1)
  (dense : ∃ K : ℕ, ∀ (p l : ℕ) (E M : Finset (Fin p × Fin l)) (C : Circuit),
    let matching := fun M : Finset (Fin p × Fin l) =>
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e=f) ∧ (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e=f);
    (∀ a c b d, a ≠ c → b ≠ d → ¬ ((a,b) ∈ E ∧ (a,d) ∈ E ∧ (c,b) ∈ E ∧ (c,d) ∈ E)) → IsAO2 (p+l) C → (∀ x, circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → M ⊆ E → matching M → (∀ T ⊆ E, matching T → T.card ≤ M.card) → (p+l+1).sqrt < M.card^2 → E.card + M.card ≤ C.size+1+K*(p+l+1).sqrt) :
  ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) → PEqualNP.TopForm.IsAO2 (x2 + x3) x6 → (∀ (x9 : Fin (x2 + x3) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3), (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) → x5 ⊆ x4 → (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) → (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) → x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨K,bound⟩ := dense
  refine ⟨max K 2,?_⟩
  intro p l E M C no4 ao computes sub rows cols
  let matching := fun T : Finset (Fin p × Fin l) =>
    Set.InjOn Prod.fst (T : Set (Fin p × Fin l)) ∧ Set.InjOn Prod.snd (T : Set (Fin p × Fin l))
  let family := E.powerset.filter matching
  have member (T) : T ∈ family ↔ T ⊆ E ∧ matching T := by simp [family]
  have mm : matching M := ⟨fun _ hx _ hy eq => rows _ hx _ hy eq,fun _ hx _ hy eq => cols _ hx _ hy eq⟩
  obtain ⟨T,ht,best⟩ := family.exists_max_image Finset.card ⟨M,(member M).mpr ⟨sub,mm⟩⟩
  obtain ⟨contained,good⟩ := (member _).mp ht
  have largest (S) (hs : S ⊆ E) (hm : matching S) : S.card ≤ T.card := best _ ((member _).mpr ⟨hs,hm⟩)
  have msize := largest M sub mm
  have all (e) (he : e ∈ E) : e.1 ∈ T.image Prod.fst ∨ e.2 ∈ T.image Prod.snd := by
    by_contra! miss
    have fresh : e ∉ T := fun h => miss.1 (mem_image_of_mem _ h)
    have extend {β : Type} [DecidableEq β] (f : Fin p × Fin l → β)
        (inj : Set.InjOn f (T : Set _)) (off : f e ∉ T.image f) :
        Set.InjOn f ((insert e T : Finset _) : Set _) := by
      intro x hx y hy eq
      rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
      · rfl
      · exact False.elim (off (eq.symm ▸ mem_image_of_mem _ hy))
      · exact False.elim (off (mem_image.mpr ⟨x,by assumption,eq⟩))
      · exact inj hx hy eq
    have impossible := largest (insert e T) (insert_subset he contained)
      ⟨extend _ good.1 miss.1,extend _ good.2 miss.2⟩
    rw [card_insert_of_notMem fresh] at impossible
    omega
  by_cases big : (p+l+1).sqrt < T.card^2
  · have unpack (S : Finset (Fin p × Fin l)) : matching S ↔
          (∀ e ∈ S, ∀ f ∈ S, e.1 = f.1 → e=f) ∧ (∀ e ∈ S, ∀ f ∈ S, e.2 = f.2 → e=f) := by
        constructor
        · intro h; exact ⟨fun _ a _ b eq => h.1 a b eq,fun _ a _ b eq => h.2 a b eq⟩
        · intro h; exact ⟨fun x a y b eq => h.1 x a y b eq,fun x a y b eq => h.2 x a y b eq⟩
    have h := bound p l E T C no4 ao computes contained ((unpack T).mp good)
      (fun S hs hS => largest S hs ((unpack S).mpr hS)) big
    have hk := Nat.mul_le_mul_right (p+l+1).sqrt (le_max_left K 2)
    omega
  · have h := periphery p l E T no4 all
    have ends := support p l E C (fun g hg => (ao.2.2 g hg).le) computes
    have hs := Nat.mul_le_mul_left 2 (Nat.le_of_not_gt big)
    have hk := Nat.mul_le_mul_right (p+l+1).sqrt (le_max_right K 2)
    omega

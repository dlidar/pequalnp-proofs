import PEqualNP.Outside.L_meta_8465

-- Specialize the lower certificate and witness of upstream L-meta-8465.
open PEqualNP.Outside.L_meta_8465 in
theorem unrestricted_lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeae8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) t) : 10 ≤ t := by
  let raw : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
  let goal : BitVec 32 := 0xeae8e880
  have root : Lower (fullMask 32) (raw.map BitVec.toNat) goal.toNat 10 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s4Stock
  have size : 10 ≤ t :=
    hcsLower (n := 5) raw goal 10 _ (by decide +kernel) (by decide +kernel) root t h
  exact size

theorem exact_negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) := by
  rintro ⟨C,hm,hs,he⟩
  have hf : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨op, ar⟩ := hm g hg
    refine ⟨?_, ar⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (Or.inl h))
  have := unrestricted_lower 9 ⟨C,hf,hs,he⟩
  omega

theorem exact_upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel


#print axioms exact_negation
#print axioms unrestricted_lower
#print axioms exact_upper

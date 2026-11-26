import ExactPool
namespace PEqualNP.Research.Pool4697
def Posted : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ)
def Necessary : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ K : Finset (Fin x1), x2.IsVertexCover ↑K ∧ x2.edgeSet.ncard + K.card ≤ x9+1
theorem posted_iff : Posted ↔ Necessary := by
  constructor
  · intro h n G inst A cubic girth iso edge b size
    letI : Nonempty (Fin n) := ⟨edge.choose⟩
    have thin := thin_of_girth G (fun v p cyc => le_trans (by decide : 5 ≤ 7) (girth v p cyc))
    obtain ⟨B,m,X,Y,built,av,correct,sz⟩ := h n G A cubic girth iso edge b size
    exact (exact_budget G thin (b+1)).mp ⟨B,m,X,Y,⟨built,av,correct⟩,sz⟩
  · intro h n G inst A cubic girth iso edge b size
    letI : Nonempty (Fin n) := ⟨edge.choose⟩
    have thin := thin_of_girth G (fun v p cyc => le_trans (by decide : 5 ≤ 7) (girth v p cyc))
    obtain ⟨B,m,X,Y,rep,sz⟩ := (exact_budget G thin (b+1)).mpr (h n G A cubic girth iso edge b size)
    exact ⟨B,m,X,Y,rep.1,rep.2.1,rep.2.2,sz⟩
end PEqualNP.Research.Pool4697

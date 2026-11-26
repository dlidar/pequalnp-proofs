import PEqualNP.Outside.L_meta_8005

namespace PEqualNP.Research.ResidualConnection6752

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8005 PEqualNP.MetaComplexity.NestedCover

-- The shared first child of reductions 859 and 452 follows from k-sandhu's merged proof.
theorem connection : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
    IsLeastAO G C → TopForm G C → (Ustar G C).Nonempty →
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty :=
  fun _ _ _ least top nonempty => residualConnection least top nonempty

-- Unordered pairs include the diagonal, representing singleton inputs.
def touched {n : Nat} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ \ (Finset.univ \ S).sym2

theorem touched_iff {n : Nat} (S : Finset (Fin n)) (u v : Fin n) :
    s(u,v) ∈ touched S ↔ u ∈ S ∨ v ∈ S := by
  by_cases h : u ∈ S <;> simp [touched, h]

theorem touched_card {n : Nat} (S : Finset (Fin n)) :
    (touched S).card = (n+1).choose 2 - (n-S.card+1).choose 2 := by
  have total := Finset.card_sym2 (Finset.univ : Finset (Fin n))
  rw [Finset.sym2_univ] at total
  simp only [Finset.card_univ,Fintype.card_fin] at total
  simp [touched, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_sym2, total]

def forced {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :=
  touched S \ G.edgeFinset

theorem forced_card {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    (forced G S).card = (n+1).choose 2 - (n-S.card+1).choose 2 -
      (touched S ∩ G.edgeFinset).card := by
  rw [← touched_card]
  rw [forced, Finset.card_sdiff, Finset.inter_comm]

theorem forced_negative {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) {u v : Fin n} (h : s(u,v) ∈ forced G S) :
    graphFun G ∅ (pairInput u v) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  exact (Finset.mem_sdiff.mp h).2 (by simpa using (graphFun_pair G u v).mp yes)

theorem forced_gate {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {g : Nat} (hg : g ∈ junk G C)
    (S : Finset (Fin n)) (shared : ∀ b : Fin 2, S ⊆ side C g b)
    {u v : Fin n} (h : s(u,v) ∈ forced G S) : gateVal n C g (pairInput u v) = true := by
  obtain ⟨len, op, _⟩ := junkData hg
  rcases (touched_iff S u v).mp (Finset.mem_sdiff.mp h).1 with hu | hv
  · exact andFromInputs ao len op (shared 0 hu) (shared 1 hu)
      (pairInput_left u v) (pairInput_left u v)
  · exact andFromInputs ao len op (shared 0 hv) (shared 1 hv)
      (pairInput_right u v) (pairInput_right u v)

-- Each side of a first-firing gate is a vertex cover of the edges first assigned to that gate.
theorem disjoint_edges_force_two {n : Nat} {C : Circuit} {g : Nat}
    {u v w z : Fin n} (hsep : Disjoint (s(u,v)).toFinset (s(w,z)).toFinset)
    (h₁ : ∀ b : Fin 2, u ∈ side C g b ∨ v ∈ side C g b)
    (h₂ : ∀ b : Fin 2, w ∈ side C g b ∨ z ∈ side C g b) (b : Fin 2) :
    2 ≤ (side (n := n) C g b).card := by
  have two {x y : Fin n} (hx : x ∈ s(u,v)) (hy : y ∈ s(w,z))
      (xs : x ∈ side C g b) (ys : y ∈ side C g b) : 2 ≤ (side (n := n) C g b).card := by
    have ne : x ≠ y := fun eq => Finset.disjoint_left.mp hsep
      (Sym2.mem_toFinset.mpr hx) (eq ▸ Sym2.mem_toFinset.mpr hy)
    have sub : ({x,y} : Finset (Fin n)) ⊆ side C g b := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact xs
      · exact ys
    simpa [ne] using Finset.card_le_card sub
  rcases h₁ b with h | h <;> rcases h₂ b with q | q
  · exact two (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _) h q
  · exact two (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _) h q
  · exact two (Sym2.mem_mk_right _ _) (Sym2.mem_mk_left _ _) h q
  · exact two (Sym2.mem_mk_right _ _) (Sym2.mem_mk_right _ _) h q

end PEqualNP.Research.ResidualConnection6752

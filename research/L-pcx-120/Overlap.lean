import SupportGraph

namespace PHPOverlap
open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge

theorem packed_leaves {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r n : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (a : Fin n → V → Bool)
    (reject : ∀ t, FalseAt C (a t) r)
    (disjoint : ∀ i j, i ≠ j → ∀ D ∈ F, ¬ LinClauseSat (a i) D → LinClauseSat (a j) D) :
    n ≤ (WithArity P r 0).card := by
  classical
  have hit (t : Fin n) : ∃ j ∈ WithArity P r 0, C j ∈ F ∧ FalseAt C (a t) j := by
    obtain ⟨j,hj,hF,hbad,w⟩ := localized_route rules (a t) le_rfl (reject t)
    have live := (live_iff rules).2 (walk_sub (fun e => e.1) w)
    exact ⟨j, by simp [WithArity, live, hj], hF,hbad⟩
  choose j mem ax bad using hit
  have inj : Function.Injective j := by
    intro u v eq
    by_contra ne
    have s := disjoint u v ne _ (ax u) (bad u)
    exact (bad v) (eq ▸ s)
  have sub : Finset.univ.image j ⊆ WithArity P r 0 := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    exact mem u
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

theorem overlap_bound {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r c d u v : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hc : c < r) (hd : d < r)
    (lc : u ≤ (WithArity P c 0).card) (ld : v ≤ (WithArity P d 0).card) :
    2*(u+v) ≤ r + (Live P c ∩ Live P d).card + 2 := by
  classical
  have cc := arity_count (fun i hi => rules i (hi.trans hc.le))
  have cd := arity_count (fun i hi => rules i (hi.trans hd.le))
  have sub : Live P c ∪ Live P d ⊆ Finset.range r := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (walk_le (bounded_edge (fun i hi => rules i (hi.trans hc.le))) ((live_iff (fun i hi => rules i (hi.trans hc.le))).mp h)) hc)
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (walk_le (bounded_edge (fun i hi => rules i (hi.trans hd.le))) ((live_iff (fun i hi => rules i (hi.trans hd.le))).mp h)) hd)
  have hu := Finset.card_le_card sub
  rw [Finset.card_range] at hu
  have he := Finset.card_union_add_card_inter (Live P c) (Live P d)
  omega

theorem ten_shared {r n common : Nat} (hr : r < n) (hn : n ≤ 51)
    (bound : 2*31 ≤ r + common + 2) : 10 ≤ common := by omega
end PHPOverlap

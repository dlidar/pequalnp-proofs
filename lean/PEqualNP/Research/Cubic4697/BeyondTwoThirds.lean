import PEqualNP.Research.Cubic4697.CubicCover
namespace PEqualNP.Research.CubicCover4697
open Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_private_pair {U I : Finset V} (sub : I ⊆ U) (fr : Free G I)
    (opt : ∀ J ⊆ U, Free G J → J.card ≤ I.card)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    {i j a b z : V} (ij : i ≠ j) (iI : i ∈ I) (jI : j ∈ I)
    (aD : a ∈ U \ I) (bD : b ∈ U \ I) (zD : z ∈ U \ I)
    (pa : I.filter (G.Adj a) = {i}) (pb : I.filter (G.Adj b) = {j})
    (pz : I.filter (G.Adj z) = {i,j}) : False := by
  classical
  have pr (x c : V) (h : I.filter (G.Adj x) = {c}) :
      G.Adj x c ∧ ∀ t ∈ I, G.Adj x t → t = c := by
    refine ⟨(mem_filter.mp (h ▸ mem_singleton_self c)).2,fun t ht adj => ?_⟩
    have u : t ∈ I.filter (G.Adj x) := mem_filter.mpr ⟨ht,adj⟩
    simpa [h] using u
  obtain ⟨ai,ha⟩ := pr a i pa
  obtain ⟨bj,hb⟩ := pr b j pb
  have zi : G.Adj z i := (mem_filter.mp (show i ∈ I.filter (G.Adj z) by simp [pz])).2
  have zj : G.Adj z j := (mem_filter.mp (show j ∈ I.filter (G.Adj z) by simp [pz])).2
  have ab : a ≠ b := fun eq => ij ((ha j jI (eq ▸ bj)).symm)
  have az : a ≠ z := fun eq => ij ((ha j jI (eq ▸ zj)).symm)
  have bz : b ≠ z := fun eq => ij (hb i iI (eq ▸ zi))
  have ib : i ≠ b := fun eq => (mem_sdiff.mp bD).2 (eq ▸ iI)
  have ja : j ≠ a := fun eq => (mem_sdiff.mp aD).2 (eq ▸ jI)
  have no_ab : ¬G.Adj a b := by
    intro edge
    let w : G.Walk i i := .cons ai.symm (.cons edge (.cons bj (.cons zj.symm (.cons zi .nil))))
    have cycle : w.IsCycle := by
      apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simp [w, SimpleGraph.Walk.isPath_def, ai.ne, bj.ne, zi.ne, zj.ne, Ne.symm, *]
      · exact (by decide : 3 ≤ 5)
    have bad := girth i w cycle
    change 7 ≤ 5 at bad
    omega
  let J := ({a,b,z} : Finset V) ∪ ((I.erase i).erase j)
  have common : ∀ x ∈ ({a,b,z} : Finset V), ∀ t ∈ (I.erase i).erase j, ¬G.Adj x t := by
    intro x hx t ht adj
    obtain ⟨nj,ht'⟩ := mem_erase.mp ht
    obtain ⟨ni,htI⟩ := mem_erase.mp ht'
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with h|h|h <;> subst x
    · exact ni (ha _ htI adj)
    · exact nj (hb _ htI adj)
    · have hh : t ∈ I.filter (G.Adj z) := mem_filter.mpr ⟨htI,adj⟩
      simp [pz,ni,nj] at hh
  have noaz := girth_no_triangle G girth i a z ai.symm zi.symm
  have nobz := girth_no_triangle G girth j b z bj.symm zj.symm
  have tiny : Free G {a,b,z} := by
    intro x hx y hy h
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      first | exact G.loopless.irrefl _ h | exact no_ab h | exact no_ab h.symm |
        exact noaz h | exact noaz h.symm | exact nobz h | exact nobz h.symm
  have freeJ : Free G J := by
    intro x hx y hy h
    rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
    · exact tiny _ hx _ hy h
    · exact common _ hx _ hy h
    · exact common _ hy _ hx h.symm
    · exact fr x (erase_subset _ _ ((erase_subset _ _) hx)) y (erase_subset _ _ ((erase_subset _ _) hy)) h
  have subJ : J ⊆ U := by
    apply union_subset
    · simp [insert_subset_iff,(mem_sdiff.mp aD).1,(mem_sdiff.mp bD).1,(mem_sdiff.mp zD).1]
    · exact (erase_subset ..).trans ((erase_subset ..).trans sub)
  have disc : Disjoint ({a,b,z} : Finset V) ((I.erase i).erase j) := by
    apply disjoint_left.mpr
    intro x hx ht
    have xi : x ∈ I := (mem_erase.mp (mem_erase.mp ht).2).2
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with h|h|h <;> subst x
    · exact (mem_sdiff.mp aD).2 xi
    · exact (mem_sdiff.mp bD).2 xi
    · exact (mem_sdiff.mp zD).2 xi
  have sz := opt J subJ freeJ
  rw [show J = _ ∪ _ from rfl,card_union_of_disjoint disc] at sz
  have sc : ({a,b,z} : Finset V).card = 3 := by simp [ab,az,bz]
  rw [sc] at sz
  have d1 := card_erase_add_one iI
  have d2 := card_erase_add_one (show j ∈ I.erase i from mem_erase.mpr ⟨ij.symm,jI⟩)
  omega

theorem nine_fourteenths [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (deg : ∀ v ∈ U, G.degree v ≤ 3)
    (active : ∀ a b, G.Adj a b → a ∈ U)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) :
    ∃ T : Finset V, (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ 14*T.card ≤ 9*U.card := by
  classical
  obtain ⟨I,sub,free,opt⟩ := max_free G U
  let D := U \ I
  let F := fun z => I.filter (G.Adj z)
  let P := D.filter fun z => (F z).card = 1
  let Q := D.filter fun z => (F z).card = 2
  let L := fun v : V => D.filter (fun z => F z = {v})
  let H := I.filter fun i => (L i).Nonempty
  have hcover (a b : V) (h : G.Adj a b) : a ∈ D ∨ b ∈ D := by
    by_cases ha : a ∈ I
    · exact Or.inr (mem_sdiff.mpr ⟨active _ _ h.symm, fun hb => free _ ha _ hb h⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨active _ _ h,ha⟩)
  have hpcount : P.card ≤ H.card := by
    have incl : P ⊆ H.biUnion L := by
      intro z hz
      obtain ⟨hd,h1⟩ := mem_filter.mp hz
      obtain ⟨v,hv⟩ := card_eq_one.mp h1
      have mem : v ∈ F z := hv ▸ mem_singleton_self v
      have l : z ∈ L v := mem_filter.mpr ⟨hd,hv⟩
      exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨(mem_filter.mp mem).1,⟨z,l⟩⟩,l⟩
    calc
      P.card ≤ (H.biUnion L).card := card_le_card incl
      _ ≤ ∑ v ∈ H, (L v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ H, 1 := sum_le_sum fun v hv => card_le_one.mpr fun a ha b hb =>
        private_unique sub free opt (girth_no_triangle G girth) (mem_filter.mp hv).1
          (mem_filter.mp ha).1 (mem_filter.mp hb).1 (mem_filter.mp ha).2 (mem_filter.mp hb).2
      _ = H.card := by simp
  have maxdeg (K : Finset V) (kI : K ⊆ I) :
      ∑ i ∈ K, (D.filter (G.Adj i)).card ≤ K.card*3 := by
    calc
      _ ≤ ∑ _u ∈ K, 3 := sum_le_sum fun u hu =>
        (card_le_card (show D.filter (G.Adj u) ⊆ G.neighborFinset u from
          fun v hv => (G.mem_neighborFinset u v).mpr (mem_filter.mp hv).2)).trans (deg u (sub (kI hu)))
      _ = _ := by simp
  have qcount : Q.card ≤ (I \ H).card*3 := by
    let M := fun i : V => D.filter (G.Adj i)
    have incl : Q ⊆ (I \ H).biUnion M := by
      intro z hz
      obtain ⟨zd,h2⟩ := mem_filter.mp hz
      obtain ⟨i,j,ij,eq⟩ := card_eq_two.mp h2
      have ia := mem_filter.mp (show i ∈ F z by simp [eq])
      have ja := mem_filter.mp (show j ∈ F z by simp [eq])
      by_cases ih : i ∈ H
      · have jh : j ∉ H := by
          intro both
          obtain ⟨a,ha⟩ := (mem_filter.mp ih).2
          obtain ⟨b,hb⟩ := (mem_filter.mp both).2
          exact no_private_pair sub free opt girth ij ia.1 ja.1
              (mem_filter.mp ha).1 (mem_filter.mp hb).1 zd (mem_filter.mp ha).2 (mem_filter.mp hb).2 eq
        exact mem_biUnion.mpr ⟨j,mem_sdiff.mpr ⟨ja.1,jh⟩,mem_filter.mpr ⟨zd,ja.2.symm⟩⟩
      · exact mem_biUnion.mpr ⟨i,mem_sdiff.mpr ⟨ia.1,ih⟩,mem_filter.mpr ⟨zd,ia.2.symm⟩⟩
    exact (card_le_card incl).trans (card_biUnion_le.trans (maxdeg _ sdiff_subset))
  have upper : ∑ z ∈ D, (F z).card ≤ I.card*3 :=
    (sum_degree_exchange D I).trans_le (maxdeg I (by rfl))
  have rows (z) (hz : z ∈ D) : 0 < (F z).card :=
    card_pos.mpr (dominates sub free opt hz)
  have lo2 : ∑ z ∈ D, (2 : ℕ) ≤ ∑ z ∈ D, ((F z).card + if (F z).card = 1 then 1 else 0) := by
    apply sum_le_sum; intro z hz; have := rows z hz; split <;> omega
  have lo3 : ∑ z ∈ D, (3 : ℕ) ≤ ∑ z ∈ D,
      (((F z).card + (if (F z).card = 1 then 1 else 0)) +
       (if (F z).card = 1 then 1 else 0) + (if (F z).card = 2 then 1 else 0)) := by
    apply sum_le_sum; intro z hz; have := rows z hz; split_ifs <;> omega
  simp only [sum_add_distrib, ← Finset.card_filter] at lo2 lo3
  have l2 : D.card*2 ≤ (∑ z ∈ D, (F z).card) + P.card := by simpa using lo2
  have l3 : D.card*3 ≤ (∑ z ∈ D, (F z).card) + P.card + P.card + Q.card := by simpa using lo3
  have activeCount : D.card + I.card = U.card := card_sdiff_add_card_eq_card sub
  have markedCount : (I \ H).card + H.card = I.card := card_sdiff_add_card_eq_card (filter_subset ..)
  exact ⟨D,hcover,by omega⟩
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- It suffices to prove the outstanding child in the smaller nine-fourteenths range. -/
theorem tighten_residual (small : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      14*(C.size+2) ≤ 14*G.edgeSet.ncard + 9*(Finset.univ \ A).card →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeSet.ncard + T.card ≤ C.size+1) : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      3*(C.size+2) ≤ 3*G.edgeSet.ncard + 2*(Finset.univ \ A).card →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeSet.ncard + T.card ≤ C.size+1 := by
  classical
  intro n G _ A C deg girth isolated edge minimal computes _
  let U := Finset.univ \ A
  by_cases cheap : 14*(C.size+2) ≤ 14*G.edgeSet.ncard + 9*U.card
  · exact small n G A C deg girth isolated edge minimal computes cheap
  · obtain ⟨T,covered,paid⟩ := nine_fourteenths G U (fun v hv => by
        rw [← G.ncard_neighborSet v, deg v (Finset.mem_sdiff.mp hv).2])
        (fun a b h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,isolated a b h⟩) girth
    exact ⟨T,covered,by omega⟩
end PEqualNP.Research.CubicCover4697

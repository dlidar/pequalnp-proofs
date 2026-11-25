import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Research.CubicCover4697
open Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Free (G : SimpleGraph V) (I : Finset V) : Prop := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

omit [DecidableEq V] in
theorem max_free (G : SimpleGraph V) (U : Finset V) :
    ∃ I ⊆ U, Free G I ∧ ∀ J ⊆ U, Free G J → J.card ≤ I.card := by
  classical
  let candidates := U.powerset.filter (Free G)
  have emp : ∅ ∈ candidates := by simp [candidates, Free]
  obtain ⟨I,hi,hm⟩ := candidates.exists_max_image Finset.card ⟨_,emp⟩
  obtain ⟨hu,hf⟩ := mem_filter.mp hi
  exact ⟨I,mem_powerset.mp hu,hf,fun J hj f => hm J (mem_filter.mpr ⟨mem_powerset.mpr hj,f⟩)⟩

theorem dominates {U I : Finset V} (sub : I ⊆ U) (f : Free G I)
    (maximal : ∀ J ⊆ U, Free G J → J.card ≤ I.card) {z : V} (hz : z ∈ U \ I) :
    (I.filter (G.Adj z)).Nonempty := by
  classical
  obtain ⟨zu,zi⟩ := mem_sdiff.mp hz
  by_contra hn
  have hno (a : V) (ha : a ∈ I) : ¬ G.Adj z a := fun h => hn ⟨a,mem_filter.mpr ⟨ha,h⟩⟩
  have fr : Free G (insert z I) := by
    intro a ha b hb h
    rcases mem_insert.mp ha with rfl|aI <;> rcases mem_insert.mp hb with rfl|bI
    · exact G.loopless.irrefl _ h
    · exact hno _ bI h
    · exact hno _ aI h.symm
    · exact f _ aI _ bI h
  have h := maximal _ (insert_subset zu sub) fr
  simp [card_insert_of_notMem zi] at h

theorem private_unique {U I : Finset V} (sub : I ⊆ U) (f : Free G I)
    (maximal : ∀ J ⊆ U, Free G J → J.card ≤ I.card)
    (noTri : ∀ a b c, G.Adj a b → G.Adj a c → ¬G.Adj b c)
    {v a b : V} (vI : v ∈ I) (ha : a ∈ U \ I) (hb : b ∈ U \ I)
    (pa : I.filter (G.Adj a) = {v}) (pb : I.filter (G.Adj b) = {v}) : a = b := by
  classical
  by_contra ab
  have aux (z : V) (p : I.filter (G.Adj z) = {v}) :
      G.Adj v z ∧ ∀ t ∈ I.erase v, ¬ G.Adj z t := by
    have mem : v ∈ I.filter (G.Adj z) := p ▸ mem_singleton_self v
    refine ⟨(mem_filter.mp mem).2.symm, ?_⟩
    intro t ht h
    have u := mem_filter.mpr ⟨(mem_erase.mp ht).2,h⟩
    rw [p,mem_singleton] at u
    exact (mem_erase.mp ht).1 u
  obtain ⟨va,an⟩ := aux a pa
  obtain ⟨vb,bn⟩ := aux b pb
  have nn := noTri v a b va vb
  have fr : Free G (insert a (insert b (I.erase v))) := by
    intro x hx y hy xy
    simp only [mem_insert] at hx hy
    rcases hx with rfl|rfl|hx <;> rcases hy with rfl|rfl|hy
    · exact G.loopless.irrefl _ xy
    · exact nn xy
    · exact an _ hy xy
    · exact nn xy.symm
    · exact G.loopless.irrefl _ xy
    · exact bn _ hy xy
    · exact an _ hx xy.symm
    · exact bn _ hx xy.symm
    · exact f _ (mem_erase.mp hx).2 _ (mem_erase.mp hy).2 xy
  have bound := maximal _ (insert_subset (mem_sdiff.mp ha).1 (insert_subset (mem_sdiff.mp hb).1 (erase_subset .. |>.trans sub))) fr
  have h1 : b ∉ I.erase v := fun h => (mem_sdiff.mp hb).2 (mem_erase.mp h).2
  have h2 : a ∉ insert b (I.erase v) := by
    simp only [mem_insert,not_or]
    exact ⟨ab,fun h => (mem_sdiff.mp ha).2 (mem_erase.mp h).2⟩
  rw [card_insert_of_notMem h2,card_insert_of_notMem h1] at bound
  have := card_erase_add_one vI
  omega

omit [DecidableEq V] in
theorem sum_degree_exchange (D I : Finset V) :
    ∑ z ∈ D, (I.filter (G.Adj z)).card = ∑ u ∈ I, (D.filter (G.Adj u)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by by_cases h : G.Adj a b <;> simp [h, G.adj_comm b a]


theorem two_thirds [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (deg : ∀ v ∈ U, G.degree v ≤ 3)
    (active : ∀ a b, G.Adj a b → a ∈ U)
    (noTri : ∀ a b c, G.Adj a b → G.Adj a c → ¬G.Adj b c) :
    ∃ T : Finset V, (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ 3*T.card ≤ 2*U.card := by
  classical
  obtain ⟨I,sub,free,opt⟩ := max_free G U
  let D := U \ I
  let F := fun z => I.filter (G.Adj z)
  let P := D.filter fun z => (F z).card = 1
  have hcover (a b : V) (h : G.Adj a b) : a ∈ D ∨ b ∈ D := by
    by_cases ha : a ∈ I
    · exact Or.inr (mem_sdiff.mpr ⟨active _ _ h.symm, fun hb => free _ ha _ hb h⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨active _ _ h,ha⟩)
  have hpcount : P.card ≤ I.card := by
    let L := fun v : V => D.filter (fun z => F z = {v})
    have incl : P ⊆ I.biUnion L := by
      intro z hz
      obtain ⟨hd,h1⟩ := mem_filter.mp hz
      obtain ⟨v,hv⟩ := card_eq_one.mp h1
      have mem : v ∈ F z := hv ▸ mem_singleton_self v
      exact mem_biUnion.mpr ⟨v,(mem_filter.mp mem).1,mem_filter.mpr ⟨hd,hv⟩⟩
    calc
      P.card ≤ (I.biUnion L).card := card_le_card incl
      _ ≤ ∑ v ∈ I, (L v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ I, 1 := sum_le_sum fun v hv => card_le_one.mpr fun a ha b hb =>
        private_unique sub free opt noTri hv (mem_filter.mp ha).1 (mem_filter.mp hb).1
          (mem_filter.mp ha).2 (mem_filter.mp hb).2
      _ = I.card := by simp
  have lower : ∑ z ∈ D, (2 : ℕ) ≤ ∑ z ∈ D, ((F z).card + if (F z).card = 1 then 1 else 0) := by
    apply sum_le_sum
    intro z hz
    have pos : 0 < (F z).card := card_pos.mpr (dominates sub free opt hz)
    split <;> omega
  have upper : ∑ z ∈ D, (F z).card ≤ I.card * 3 := by
    rw [show (∑ z ∈ D, (F z).card) = ∑ u ∈ I, (D.filter (G.Adj u)).card from sum_degree_exchange D I]
    calc
      _ ≤ ∑ _u ∈ I, 3 := sum_le_sum fun u hu =>
        (card_le_card (show D.filter (G.Adj u) ⊆ G.neighborFinset u from
          fun v hv => (G.mem_neighborFinset u v).mpr (mem_filter.mp hv).2)).trans (deg u (sub hu))
      _ = _ := by simp
  rw [sum_add_distrib, ← Finset.card_filter] at lower
  change (∑ _z ∈ D, (2 : ℕ)) ≤ _ + P.card at lower
  have lowerNat : D.card * 2 ≤ (∑ z ∈ D, (F z).card) + P.card := by simpa using lower
  clear lower
  have partition : D.card + I.card = U.card := card_sdiff_add_card_eq_card sub
  exact ⟨D,hcover,by omega⟩

omit [DecidableEq V] in
theorem girth_no_triangle (G : SimpleGraph V)
    (h : ∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) :
    ∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c := by
  intro a b c ab ac bc
  let w : G.Walk a a := .cons ab (.cons bc (.cons ac.symm .nil))
  have cyc : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [w,SimpleGraph.Walk.isPath_def, ab.ne.symm, ac.ne.symm, bc.ne]
    · exact Nat.le_refl 3
  have bad := h a w cyc
  change 7 ≤ 3 at bad
  omega

theorem packing_child : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)),
      (∀ v ∈ U, G.degree v ≤ 3) → (∀ a b, G.Adj a b → a ∈ U) →
      (∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c) →
      ∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ 3*T.card ≤ 2*U.card := by
  intro n G _ U
  exact two_thirds G U
end PEqualNP.Research.CubicCover4697

import PEqualNP.Defs
import Mathlib.Tactic
namespace PEqualNP.Research.StarPools4697
open Finset
variable {V : Type*} [DecidableEq V]

def Available (B : List (Finset V)) (S : Finset V) := S.card ≤ 1 ∨ S ∈ B
def Valid (B : List (Finset V)) : Prop :=
  ∀ (P : List (Finset V)) (a : Finset V) (T : List (Finset V)), B = P ++ a :: T →
      ∃ b c, a = b ∪ c ∧ Available T b ∧ Available T c

omit [DecidableEq V] in
theorem available_append_left {B : List (Finset V)} (D : List (Finset V)) {S} :
    Available B S → Available (B++D) S := by
  unfold Available
  simp only [List.mem_append]
  tauto

omit [DecidableEq V] in
theorem available_append_right (B : List (Finset V)) {D : List (Finset V)} {S} :
    Available D S → Available (B++D) S := by
  unfold Available
  simp only [List.mem_append]
  tauto

theorem valid_nil : Valid ([] : List (Finset V)) := by simp [Valid]
theorem valid_cons (a : Finset V) (D : List (Finset V)) :
    Valid (a::D) ↔ Valid D ∧ ∃ b c, a = b ∪ c ∧ Available D b ∧ Available D c := by
  constructor
  · intro h
    exact ⟨fun P x T e => h (a::P) x T (by simp [e]), h [] a D rfl⟩
  · rintro ⟨vd,bc⟩ P x T e
    cases P with
    | nil => cases e; exact bc
    | cons u P => exact vd P x T (List.cons.inj e).2

theorem valid_append {B D : List (Finset V)} (b : Valid B) (d : Valid D) : Valid (B++D) := by
  induction B with
  | nil => exact d
  | cons a B ih =>
    obtain ⟨vb,x,y,e,hx,hy⟩ := (valid_cons ..).mp b
    exact (valid_cons ..).mpr ⟨ih vb,x,y,e,available_append_left D hx,available_append_left D hy⟩

theorem aggregate (S : Finset V) :
    ∃ B : List (Finset V), Valid B ∧ Available B S ∧ B.length ≤ S.card-1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[],valid_nil,Or.inl (by simp),by simp⟩
  | @insert a S hn ih =>
    obtain ⟨B,vb,av,len⟩ := ih
    by_cases emp : S = ∅
    · subst S
      exact ⟨[],valid_nil,Or.inl (by simp),by simp⟩
    · refine ⟨insert a S :: B,(valid_cons ..).mpr ⟨vb,{a},S,by simp,Or.inl (by simp),av⟩,
        Or.inr (by simp),?_⟩
      rw [List.length_cons,card_insert_of_notMem hn]
      have hpos := card_pos.mpr (nonempty_iff_ne_empty.mpr emp)
      omega

/-- Each unordered edge is assigned to the first cover vertex it meets. -/
theorem owned_stars {n : ℕ} (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)),
    (∀ e ∈ E, ∃ a ∈ T, a ∈ e) →
    ∃ L : List (Fin n × Finset (Fin n)),
      (∀ p ∈ L, p.2.Nonempty) ∧ L.length ≤ T.card ∧
      (L.map fun p => p.2.card).sum ≤ E.card ∧
      ∀ e, e ∈ E ↔ ∃ p ∈ L, ∃ b ∈ p.2, e = s(p.1,b) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro E cov
    have emp : E = ∅ := eq_empty_iff_forall_notMem.mpr fun e he => by simpa using cov e he
    subst E
    exact ⟨[],by simp⟩
  | @insert t T ht ih =>
    intro E cov
    let F := E.filter fun e => t ∈ e
    let R := E.filter fun e => t ∉ e
    let S := univ.filter fun v : Fin n => s(t,v) ∈ F
    have parts : F.card + R.card = E.card := card_filter_add_card_filter_not _
    have price : S.card ≤ F.card := by
      apply card_le_card_of_injOn (fun v => s(t,v))
      · intro v hv
        exact (mem_filter.mp hv).2
      · exact fun a _ b _ hab => Sym2.congr_right.mp hab
    obtain ⟨L,ne,size,cost,spec⟩ := ih R (by
      intro e he
      obtain ⟨a,ha,hmem⟩ := cov e (mem_filter.mp he).1
      refine ⟨a,?_,hmem⟩
      rcases mem_insert.mp ha with rfl|h
      · exact False.elim ((mem_filter.mp he).2 hmem)
      · exact h)
    have localSpec (e) : e ∈ F ↔ ∃ b ∈ S, e = s(t,b) := by
      constructor
      · intro he
        obtain ⟨b,h⟩ := Sym2.mem_iff_exists.mp (mem_filter.mp he).2
        exact ⟨b,mem_filter.mpr ⟨mem_univ _,h ▸ he⟩,h⟩
      · rintro ⟨b,hb,rfl⟩; exact (mem_filter.mp hb).2
    have split (e) : e ∈ E ↔ e ∈ F ∨ e ∈ R := by simp [F,R]; tauto
    rw [card_insert_of_notMem ht]
    by_cases nonempty : S.Nonempty
    · refine ⟨(t,S)::L,?_,by simp; omega,by simp; omega,?_⟩
      · intro p h
        rcases List.mem_cons.mp h with rfl|h
        · exact nonempty
        · exact ne p h
      · intro e
        rw [split,localSpec,spec]
        simp only [List.mem_cons]
        constructor
        · rintro (h|⟨p,hp,h⟩)
          · exact ⟨(t,S),Or.inl rfl,h⟩
          · exact ⟨p,Or.inr hp,h⟩
        · rintro ⟨p,rfl|hp,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨p,hp,h⟩
    · refine ⟨L,ne,by omega,by omega,?_⟩
      intro e
      rw [split,localSpec,spec]
      have hn (b : Fin n) : b ∉ S := fun h => nonempty ⟨b,h⟩
      simp [hn]

theorem pool_stars (L : List (V × Finset V)) (ne : ∀ p ∈ L, p.2.Nonempty) :
    ∃ B : List (Finset V), Valid B ∧ (∀ p ∈ L, Available B p.2) ∧
        B.length + L.length ≤ (L.map fun p => p.2.card).sum := by
  induction L with
  | nil => exact ⟨[],valid_nil,by simp⟩
  | cons p L ih =>
    obtain ⟨D,dv,da,dl⟩ := ih (fun q h => ne q (List.mem_cons_of_mem p h))
    obtain ⟨B,bv,ba,bl⟩ := aggregate p.2
    refine ⟨B++D, valid_append bv dv,?_,?_⟩
    · intro q h
      rcases List.mem_cons.mp h with rfl|l
      · exact available_append_left D ba
      · exact available_append_right B (da q l)
    · have := (ne p List.mem_cons_self).card_pos
      simp only [List.length_append,List.length_cons,List.map_cons,List.sum_cons]
      omega

theorem build_child : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (D : List (Finset (Fin n))),
        B = P ++ a :: D → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧
          (b.card ≤ 1 ∨ b ∈ D) ∧ (c.card ≤ 1 ∨ c ∈ D)) ∧
      (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
      (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
      B.length + 2 * m ≤ G.edgeSet.ncard + T.card := by
  classical
  intro n G _ T hc
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with ha|hb
    · exact ⟨a,ha,Sym2.mem_mk_left ..⟩
    · exact ⟨b,hb,Sym2.mem_mk_right ..⟩
  obtain ⟨L,ne,num,total,edges⟩ := owned_stars T _ cov
  obtain ⟨B,vb,av,price⟩ := pool_stars L ne
  refine ⟨B,L.length,fun i => {(L.get i).1},fun i => (L.get i).2,vb,?_,?_,?_⟩
  · intro i
    exact ⟨Or.inl (by simp),av _ (List.get_mem ..)⟩
  · intro x
    constructor
    · rintro ⟨i,⟨u,hu,on⟩,v,hv,lit⟩
      simp only [Finset.mem_singleton] at hu
      subst u
      refine ⟨(L.get i).1,v,?_,on,lit⟩
      have h := (edges s((L.get i).1,v)).mpr ⟨L.get i,List.get_mem ..,v,hv,rfl⟩
      simpa using h
    · rintro ⟨a,b,ab,xa,xb⟩
      obtain ⟨p,hp,v,hv,ee⟩ := (edges s(a,b)).mp (by simpa using ab)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
      subst p
      refine ⟨i,⟨(L.get i).1,Finset.mem_singleton_self _,?_⟩,v,hv,?_⟩
      · rcases Sym2.eq_iff.mp ee with h|h
        · exact (congrArg x h.1.symm).trans xa
        · exact (congrArg x h.2.symm).trans xb
      · rcases Sym2.eq_iff.mp ee with h|h
        · exact (congrArg x h.2.symm).trans xb
        · exact (congrArg x h.1.symm).trans xa
  · have same : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    omega
end PEqualNP.Research.StarPools4697

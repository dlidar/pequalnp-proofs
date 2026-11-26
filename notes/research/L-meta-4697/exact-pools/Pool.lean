import LeafCount
namespace PEqualNP.Research.Pool4697
open Finset
variable {V : Type} [DecidableEq V] [Fintype V]

def Built (B : List (Finset V)) := ∀ P a D, B = P ++ a :: D →
  ∃ b c : Finset V, a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ D) ∧ (c.card ≤ 1 ∨ c ∈ D)

theorem layout (B : List (Finset V)) (built : Built B) :
    ∃ (n : Nat) (W : Nat → Finset V),
    (∀ i < n,(W i).card ≤ 1) ∧
    (∀ j < B.length,∃ a b, a < n+j ∧ b < n+j ∧ W (n+j)=W a ∪ W b) ∧
    ∀ t : Finset V, t.card ≤ 1 ∨ t ∈ B → ∃ i < n+B.length, W i=t := by
  classical
  induction B with
  | nil =>
    let e := Fintype.equivFin (Finset V)
    let W (i : Nat) : Finset V := if h : i < Fintype.card (Finset V) then
      let S := e.symm ⟨i,h⟩
      if S.card ≤ 1 then S else ∅ else ∅
    refine ⟨Fintype.card (Finset V),W,?_,by simp,?_⟩
    · intro i hi
      simp only [W,dif_pos hi]
      split <;> simp_all
    · intro t ht
      simp only [List.not_mem_nil,or_false] at ht
      exact ⟨(e t).val,by simpa using (e t).isLt,by dsimp only [W]; rw [dif_pos (e t).isLt]; simp [ht]⟩
  | cons s D ih =>
    have tailB : Built D := fun P a E eq => built (s::P) a E (by simp [eq])
    obtain ⟨n,W,raw,gate,find⟩ := ih tailB
    obtain ⟨b,c,join,hb,hc⟩ := built [] s D rfl
    obtain ⟨p,lp,ep⟩ := find _ hb
    obtain ⟨q,lq,eq⟩ := find _ hc
    let N := n+D.length
    let W' (i : Nat) := if i=N then s else W i
    have old {i} (h : i < n+D.length) : W' i = W i := if_neg (Nat.ne_of_lt h)
    refine ⟨n,W',fun i hi => by rw [old (by omega)]; exact raw i hi,?_,?_⟩
    · intro j hj
      simp only [List.length_cons] at hj
      by_cases last : j = D.length
      · subst j
        exact ⟨p,q,lp,lq,by simpa [W',N,lp.ne,lq.ne,ep,eq] using join⟩
      · have prev : j < D.length := by omega
        obtain ⟨a,b,ha,hb,hw⟩ := gate j prev
        exact ⟨a,b,ha,hb,by rw [old (by omega),old (by omega : a < n+D.length),old (by omega : b < n+D.length),hw]⟩
    · intro t ht
      by_cases last : t=s
      · subst t; exact ⟨N,by simp [N],by simp [W']⟩
      · obtain ⟨i,hi,eq⟩ := find t (by simpa [List.mem_cons,last] using ht)
        exact ⟨i,by simp only [List.length_cons]; omega,(old hi).trans eq⟩

theorem pair_edges {G : SimpleGraph V} {m : Nat} {X Y : Fin m → Finset V}
    (correct : ∀ x : V → Bool, (∃ i, (∃ u ∈ X i,x u=true) ∧ ∃ v ∈ Y i,x v=true) ↔
      ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true) :
    (∀ i, ∀ a ∈ X i,∀ b ∈ Y i,G.Adj a b) ∧
    (∀ a b,G.Adj a b → ∃ i,(a∈X i ∧ b∈Y i) ∨ (b∈X i ∧ a∈Y i)) := by
  have cross (i) (a) (ha : a ∈ X i) (b) (hb : b ∈ Y i) : G.Adj a b := by
    obtain ⟨u,v,uv,hu,hv⟩ := (correct (fun z => decide (z=a ∨ z=b))).mp
      ⟨i,⟨a,ha,by simp⟩,b,hb,by simp⟩
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> first | exact uv | exact uv.symm | exact (uv.ne rfl).elim
  refine ⟨cross,?_⟩
  intro a b ab
  obtain ⟨i,⟨u,hu,eu⟩,v,hv,ev⟩ := (correct (fun z => decide (z=a ∨ z=b))).mpr
    ⟨a,b,ab,by simp,by simp⟩
  have ne := (cross i u hu v hv).ne
  simp only [decide_eq_true_eq] at eu ev
  refine ⟨i,?_⟩
  rcases eu with rfl|rfl <;> rcases ev with rfl|rfl <;> tauto
end PEqualNP.Research.Pool4697

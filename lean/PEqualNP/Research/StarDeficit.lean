import Mathlib
namespace PEqualNP.Research.StarDeficit
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
def Covers (G : SimpleGraph V) (T : Finset V) := ∀ a b,G.Adj a b → a∈T ∨ b∈T
private theorem inhabited_cost (G : SimpleGraph V) : ∃ k : ℕ, ∃ T : Finset V,Covers G T ∧ T.card = k :=
  ⟨_,univ,fun a _ _ => Or.inl (mem_univ a),rfl⟩
noncomputable def tau (G : SimpleGraph V) : ℕ := by classical exact Nat.find (inhabited_cost G)
theorem attain (G : SimpleGraph V) : ∃ T : Finset V,Covers G T ∧ T.card = tau G := by
  classical exact Nat.find_spec (inhabited_cost G)
theorem optimal {G : SimpleGraph V} {T : Finset V} (c : Covers G T) : tau G ≤ T.card := by
  classical exact Nat.find_min' (inhabited_cost G) ⟨T,c,rfl⟩
def pin (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a∉S ∧ b∉S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem strip {G : SimpleGraph V} {T : Finset V} (c : Covers G T) (S : Finset V) :
    Covers (pin G S) (T \ S) := by
  intro a b h
  rcases c a b h.1 with ha|hb
  · exact Or.inl (mem_sdiff.mpr ⟨ha,h.2.1⟩)
  · exact Or.inr (mem_sdiff.mpr ⟨hb,h.2.2⟩)
theorem restore {G : SimpleGraph V} {T S : Finset V} (c : Covers (pin G S) T) : Covers G (T∪S) := by
  intro a b hab
  by_cases ha : a∈S
  · exact Or.inl (mem_union_right _ ha)
  by_cases hb : b∈S
  · exact Or.inr (mem_union_right _ hb)
  exact (c a b ⟨hab,ha,hb⟩).imp (mem_union_left _) (mem_union_left _)
theorem interval (G : SimpleGraph V) (S : Finset V) :
    tau (pin G S) ≤ tau G ∧ tau G ≤ tau (pin G S) + S.card := by
  obtain ⟨T,c,sz⟩ := attain G
  obtain ⟨U,cu,su⟩ := attain (pin G S)
  exact ⟨(optimal (strip c S)).trans ((card_le_card sdiff_subset).trans sz.le),
    (optimal (restore cu)).trans ((card_union_le ..).trans (by omega))⟩
theorem loss_eq_iff (G : SimpleGraph V) (S : Finset V) :
    tau (pin G S) + S.card = tau G ↔ ∃ T : Finset V,Covers G T ∧ T.card=tau G ∧ S⊆T := by
  constructor
  · intro h
    obtain ⟨U,cu,sz⟩ := attain (pin G S)
    have c := restore cu
    exact ⟨U∪S,c,le_antisymm ((card_union_le ..).trans (by omega)) (optimal c),subset_union_right⟩
  · rintro ⟨T,c,sz,sub⟩
    have lo := (interval G S).2
    have hi := optimal (strip c S)
    have eq := card_sdiff_add_card_eq_card sub
    omega
theorem pin_single (G : SimpleGraph V) (v : V) : pin G {v} = G.deleteIncidenceSet v := by
  ext a b; simp [pin,SimpleGraph.deleteIncidenceSet_adj]
-- The score is the conventional star-cover size plus one.
noncomputable def score (G : SimpleGraph V) [DecidableRel G.Adj] (marked : Nat) :=
  marked + G.edgeFinset.card + tau G
theorem score_interval (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (a : Nat) :
    score (G.deleteIncidenceSet v) a + G.degree v ≤ score G a ∧
    score G a ≤ score (G.deleteIncidenceSet v) a + G.degree v + 1 := by
  have h := interval G {v}
  rw [pin_single,card_singleton] at h
  have hc := card_le_card (G.incidenceFinset_subset v)
  rw [G.card_incidenceFinset_eq_degree] at hc
  simp only [score,G.card_edgeFinset_deleteIncidenceSet];omega
theorem full_saving_iff (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (a : Nat) :
    score (G.deleteIncidenceSet v) a + G.degree v + 1 = score G a ↔
    ∃ T : Finset V,Covers G T ∧ T.card=tau G ∧ v∈T := by
  have h := loss_eq_iff G {v};rw [pin_single,card_singleton] at h
  simp only [singleton_subset_iff] at h
  rw [← h]
  have hc := card_le_card (G.incidenceFinset_subset v)
  rw [G.card_incidenceFinset_eq_degree] at hc
  simp only [score,G.card_edgeFinset_deleteIncidenceSet];omega
theorem cofactor_must_beat_stars (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (a parent child : Nat)
    (deg : G.degree v = 3) (below : parent+1 < score G a) (save : child+4 ≤ parent) :
    child+1 < score (G.deleteIncidenceSet v) a := by
  have h := (score_interval G v a).2
  omega
noncomputable def deficit (G : SimpleGraph V) [DecidableRel G.Adj] (a gates : Nat) : Int :=
  (score G a : Int) - gates - 1
open Classical in
theorem saving_test (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (a s t : Nat)
    (deg : G.degree v=3) : t+4 ≤ s ↔
    deficit G a s + (if ∃ T : Finset V,Covers G T ∧ T.card=tau G ∧ v∈T then (0:Int) else 1) ≤
      deficit (G.deleteIncidenceSet v) a t := by
  classical
  have h := score_interval G v a
  have iff := full_saving_iff G v a
  simp only [deficit]
  split_ifs with hT
  · have := iff.mpr hT;omega
  · have := mt iff.mp hT;omega
end PEqualNP.Research.StarDeficit

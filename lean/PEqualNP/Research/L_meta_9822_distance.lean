import PEqualNP.Research.L_meta_9822_graph_data
namespace PEqualNP.Research.GraphDistance
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PuncturedPetersen
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem witnesses {G : Graph} {e : Edge} (he : e ∈ G) : added e ⊆ errors G := by
  intro x hx
  obtain ⟨hc,off⟩ : contained e x = true ∧ ¬ active base x := by simpa [added] using hx
  have on : active G x := ⟨e,he,hc⟩
  simp [errors,off,on]

theorem missing {G : Graph} {e : Edge} (sub : G ⊆ base) (he : e ∉ G) : lost e ⊆ errors G := by
  intro x hx
  obtain ⟨on,off⟩ : active base x ∧ ¬ active (base.erase e) x := by simpa [lost] using hx
  have miss : ¬ active G x := by
    rintro ⟨f,hf,hit⟩
    exact off ⟨f,Finset.mem_erase.mpr ⟨by rintro rfl; exact he hf,sub hf⟩,hit⟩
  simp [errors,on,miss]

theorem only_add_errors (e : Edge) : errors (insert e base) = added e := by
  ext x
  by_cases on : active base x
  · have on' : active (insert e base) x := by
      obtain ⟨a,ha,hb⟩ := on; exact ⟨a,Finset.mem_insert_of_mem ha,hb⟩
    simp [errors,added,on,on']
  · have iff' : active (insert e base) x ↔ contained e x = true := by
      constructor
      · rintro ⟨a,ha,hb⟩
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hb
        · exact (on ⟨a,ha,hb⟩).elim
      · intro hh; exact ⟨e,Finset.mem_insert_self _ _,hh⟩
    simp [errors,added,iff',on]

theorem distance (G : Graph) (ne : G ≠ base) : 5 ≤ (errors G).card := by
  by_cases sub : G ⊆ base
  · obtain ⟨e,he,ha⟩ := Finset.not_subset.mp (show ¬base ⊆ G from fun h => ne (Finset.Subset.antisymm sub h))
    exact le_trans (by have := per_deletion e he; omega) (Finset.card_le_card (missing sub ha))
  · obtain ⟨e,he,ha⟩ := Finset.not_subset.mp sub
    exact (per_add e ha).1.trans (Finset.card_le_card (witnesses he))

theorem sharp_iff (G : Graph) : (errors G).card = 5 ↔ ∃ e ∈ five, G = insert e base := by
  constructor
  · intro h
    by_cases sub : G ⊆ base
    · by_cases same : base ⊆ G
      · have eq := Finset.Subset.antisymm sub same
        subst G; simp [errors] at h
      · obtain ⟨e,he,ha⟩ := Finset.not_subset.mp same
        have hh := (per_deletion e he).trans (Finset.card_le_card (missing sub ha)); omega
    · obtain ⟨e,he,ha⟩ := Finset.not_subset.mp sub
      have lb := (per_add e ha).1
      have inc := witnesses he
      have eq : added e = errors G := Finset.eq_of_subset_of_card_le inc (by omega)
      refine ⟨e,(per_add e ha).2.mp (by rw [eq,h]),?_⟩
      ext f
      by_cases same : e=f
      · subst f; simp [he]
      · have none : alone f ∉ added e := by simp [added,isolated_pair,Ne.symm same]
        rw [eq] at none
        have agree : f ∈ G ↔ f ∈ base := by
          simpa [errors,alone_active] using none
        simpa [Ne.symm same] using agree
  · rintro ⟨e,he,rfl⟩
    have dis : ∀ z ∈ five, z ∉ base := by decide +kernel
    rw [only_add_errors]; exact (per_add e (dis e he)).2.mpr he

def exact18 : Circuit := ⟨[⟨.and,[3,8]⟩,
   ⟨.or,[2,9]⟩,
   ⟨.and,[7,11]⟩,
   ⟨.or,[1,8]⟩,
   ⟨.or,[13,9]⟩,
   ⟨.and,[6,14]⟩,
   ⟨.and,[1,2]⟩,
   ⟨.or,[0,7]⟩,
   ⟨.or,[17,8]⟩,
   ⟨.and,[5,18]⟩,
   ⟨.or,[0,3]⟩,
   ⟨.or,[20,9]⟩,
   ⟨.and,[4,21]⟩,
   ⟨.or,[10,12]⟩,
   ⟨.or,[23,15]⟩,
   ⟨.or,[24,16]⟩,
   ⟨.or,[25,19]⟩,
   ⟨.or,[26,22]⟩],27⟩

def near17 : Circuit := ⟨[⟨.or,[5,6]⟩,
   ⟨.or,[7,8]⟩,
   ⟨.and,[10,11]⟩,
   ⟨.or,[4,6]⟩,
   ⟨.or,[13,7]⟩,
   ⟨.and,[14,9]⟩,
   ⟨.or,[4,8]⟩,
   ⟨.and,[3,16]⟩,
   ⟨.or,[2,6]⟩,
   ⟨.or,[1,7]⟩,
   ⟨.and,[18,19]⟩,
   ⟨.or,[4,5]⟩,
   ⟨.and,[0,21]⟩,
   ⟨.or,[12,15]⟩,
   ⟨.or,[23,17]⟩,
   ⟨.or,[24,20]⟩,
   ⟨.or,[25,22]⟩],26⟩
theorem exact18_checked : Monotone2 exact18 ∧ exact18.size = 18 ∧
    ∀ x : Fin 10 → Bool, exact18.eval (List.ofFn x) = targetBits x := by
  exact ⟨by simp [Monotone2,exact18],rfl,by decide +kernel⟩
theorem near17_checked : Monotone2 near17 ∧ near17.size = 17 ∧
    ∀ x : Fin 10 → Bool, near17.eval (List.ofFn x) = (targetBits x || (x 6 && x 7)) := by
  exact ⟨by simp [Monotone2,near17],rfl,by decide +kernel⟩
theorem affected : (Finset.univ.filter fun x : Input => near17.eval (List.ofFn (fun i : Fin 10 => x.val.testBit i.val)) != target x.val)
    = {192,193,200,201,208} := by decide +kernel
end PEqualNP.Research.GraphDistance

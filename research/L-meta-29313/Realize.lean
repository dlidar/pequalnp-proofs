import Bridge
namespace InverterBridge

/-- An incomparable two-colour sample is realized by a monotone output and one antitone
signal passed through a monotone AND/OR decoder. Every exact replacement fits all samples. -/
theorem realize_labels {I : Type} [Fintype I] (Z O : Finset (X I))
    (sep : ∀ z∈Z,∀ o∈O,¬z≤o ∧ ¬o≤z) :
    ∃ (A B F G : X I → Bool), Monotone A ∧ Monotone B ∧ Monotone F ∧ Antitone G ∧
      (∀ x,(B x || (A x && G x)) = F x) ∧
      (∀ k : X I → Bool, (∀ x,(B x || (A x && k x)) = F x) →
        (∀ z∈Z,k z=false) ∧ (∀ o∈O,k o=true)) := by
  classical
  let A (x : X I) := decide (∃ y,y∈Z ∪ O ∧ y≤x)
  let B (x : X I) := decide (¬ ∃ y,y∈Z ∪ O ∧ x≤y)
  let U (x : X I) := decide (∃ o,o∈O ∧ o≤x)
  let G (x : X I) := decide (∃ o,o∈O ∧ x≤o)
  have am : Monotone A := by
    intro x y le;cases ax : A x with
    | false => exact bot_le
    | true =>
      obtain ⟨a,ha,ax⟩ := of_decide_eq_true ax
      exact le_of_eq (decide_eq_true ⟨a,ha,ax.trans le⟩).symm
  have bm : Monotone B := by
    intro x y le;cases bx : B x with
    | false => exact bot_le
    | true =>
      apply le_of_eq;apply Eq.symm;apply decide_eq_true
      rintro ⟨a,ha,ya⟩;exact of_decide_eq_true bx ⟨a,ha,le.trans ya⟩
  have um : Monotone U := by
    intro x y le;cases ux : U x with
    | false => exact bot_le
    | true =>
      obtain ⟨a,ha,ax⟩ := of_decide_eq_true ux
      exact le_of_eq (decide_eq_true ⟨a,ha,ax.trans le⟩).symm
  have gm : Antitone G := by
    intro x y le;cases gy : G y with
    | false => exact bot_le
    | true =>
      obtain ⟨a,ha,ya⟩ := of_decide_eq_true gy
      exact le_of_eq (decide_eq_true ⟨a,ha,le.trans ya⟩).symm
  let F (x : X I) := B x || (A x && U x)
  refine ⟨A,B,F,G,am,bm,?_,gm,?_,?_⟩
  · exact fun x y xy => sup_le_sup (bm xy) (inf_le_inf (am xy) (um xy))
  · intro x;unfold F
    by_cases a : A x=true <;> by_cases b : B x=false
    · simp only [b,a,Bool.false_or,Bool.true_and]
      obtain ⟨lo,hlo,le⟩ := of_decide_eq_true a
      have ex : ∃ hi,hi∈Z∪O ∧ x≤hi := by simpa [B] using b
      obtain ⟨hi,hhi,ge⟩ := ex
      apply Bool.eq_iff_iff.mpr;constructor
      · intro gx;obtain ⟨o,ho,xo⟩ := of_decide_eq_true gx
        rcases Finset.mem_union.mp hlo with hz|ho'
        · exact False.elim ((sep lo hz o ho).1 (le.trans xo))
        · exact decide_eq_true ⟨lo,ho',le⟩
      · intro ux;obtain ⟨o,ho,ox⟩ := of_decide_eq_true ux
        rcases Finset.mem_union.mp hhi with hz|ho'
        · exact False.elim ((sep hi hz o ho).2 (ox.trans ge))
        · exact decide_eq_true ⟨hi,ho',ge⟩
    all_goals simp_all
  · intro k ok
    have at_sample (y : X I) (hy : y∈Z∪O) : k y=U y := by
      have a : A y=true := decide_eq_true ⟨y,hy,le_rfl⟩
      have b : B y=false := by apply decide_eq_false; exact fun no => no ⟨y,hy,le_rfl⟩
      simpa only [F,a,b,Bool.false_or,Bool.true_and] using ok y
    constructor
    · intro z hz;rw [at_sample z (Finset.mem_union_left _ hz)]
      apply decide_eq_false; rintro ⟨o,ho,oz⟩;exact (sep z hz o ho).2 oz
    · intro o ho;rw [at_sample o (Finset.mem_union_right _ ho)];exact decide_eq_true ⟨o,ho,le_rfl⟩
end InverterBridge

import PEqualNP.Defs

theorem PEqualNP.Research.L_meta_4289_support : ∀ (N s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))), o < N + N + s →
    (∀ j < s, ∃ a b : ℕ, max a b < N + N + j ∧ W (N+N+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
    ∃ T : Finset ℕ, (∀ i ∈ T, i < N+N) ∧ T.card ≤ s+1 ∧
      ∀ u v : (Fin N → Bool) × (Fin N → Bool), (∀ i ∈ T, u ∈ W i ↔ v ∈ W i) → (u ∈ W o ↔ v ∈ W o) := by
  intro N s o W ho gates
  classical
  let n := N+N
  have cut (m : ℕ) (hm : m ≤ s) (F : Finset ℕ) (bounded : ∀ i ∈ F, i < n+m) :
      ∃ T : Finset ℕ, (∀ i ∈ T, i < n) ∧ T.card ≤ m+F.card ∧
        ∀ u v : (Fin N → Bool) × (Fin N → Bool), (∀ i ∈ T, u ∈ W i ↔ v ∈ W i) →
        ∀ i ∈ F, u ∈ W i ↔ v ∈ W i := by
    induction m generalizing F with
    | zero => exact ⟨F,by simpa using bounded,by simp,fun _ _ a => a⟩
    | succ m ih =>
      let k := n+m
      by_cases hit : k ∈ F
      · obtain ⟨a,b,h,kind⟩ := gates m (by omega)
        change max a b < k at h
        let G := insert a (insert b (F.erase k))
        have gb : ∀ i ∈ G, i < n+m := by
          intro i hi
          simp only [G,Finset.mem_insert,Finset.mem_erase] at hi
          rcases hi with rfl|rfl|⟨ne,hi⟩
          · exact lt_of_le_of_lt (le_max_left _ _) h
          · exact lt_of_le_of_lt (le_max_right _ _) h
          · have := bounded i hi
            dsimp [k] at ne
            omega
        obtain ⟨T,ht,hn,det⟩ := ih (by omega) G gb
        have size : G.card ≤ F.card+1 := by
          have ha := Finset.card_insert_le a (insert b (F.erase k))
          have hb := Finset.card_insert_le b (F.erase k)
          have hp := Finset.card_pos.mpr ⟨k,hit⟩
          rw [Finset.card_erase_of_mem hit] at hb
          dsimp [G]; omega
        refine ⟨T,ht,by omega,?_⟩
        intro u v same i hi
        by_cases ei : i = k
        · subst i
          have da := det u v same a (by simp [G])
          have db := det u v same b (by simp [G])
          change W k ∈ _ at kind
          simp only [List.mem_cons,List.not_mem_nil,or_false] at kind
          rcases kind with e|e|e|e <;> rw [e]
          · exact or_congr da db
          · exact da
          · rfl
          · exact and_congr da db
        · exact det u v same i (by simp [G,ei,hi])
      · have fb : ∀ i ∈ F, i < n+m := by
          intro i hi
          have := bounded i hi
          have ne : i ≠ n+m := fun e => hit (show n+m ∈ F from e ▸ hi)
          omega
        obtain ⟨T,ht,hn,det⟩ := ih (by omega) F fb
        exact ⟨T,ht,by omega,det⟩
  obtain ⟨T,ht,hn,det⟩ := cut s le_rfl {o} (by simpa [n] using ho)
  exact ⟨T,ht,by simpa using hn,fun u v same => det u v same o (by simp)⟩

-- For any incidence relation without isolated points or lines, all 2N input
-- coordinates are necessary. Rejecting the maximal safe tests for zero lines
-- and singleton lines is sufficient for this gate-count bound.
theorem PEqualNP.Research.incidence_input_bound
    (N q s o : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (hq : 1 ≤ q)
    (rows : ∀ p, ∃ l, I p l) (cols : ∀ l, ∃ p, I p l) :
    let n := N+N
    let one := fun (p t : Fin N) => decide (t=p)
    o < n+s →
    (∀ i : Fin N, W i = {v | v.1 i = true} ∧ W (N+i.val) = {v | v.2 i = true}) →
    (∀ j < s, ∃ a b, max a b < n+j ∧ W (n+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
    (∀ p l, I p l → (one p,one l) ∈ W o) →
    (∀ B : Fin N → Bool, Fintype.card {l // B l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ B l = true)), B) ∉ W o) →
    2*N ≤ s+1 := by
  intro n one ho raw gates pos neg
  classical
  let zero : Fin N → Bool := fun _ => false
  have mono : ∀ k < n+s, ∀ u v : (Fin N → Bool) × (Fin N → Bool),
      (∀ i, u.1 i = true → v.1 i = true) → (∀ i, u.2 i = true → v.2 i = true) →
      u ∈ W k → v ∈ W k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk u v hp hl mem
      by_cases h : k < N
      · rw [(raw ⟨k,h⟩).1] at mem ⊢
        exact hp _ mem
      by_cases h' : k < n
      · have small : k-N < N := by dsimp [n] at h'; omega
        have eq : k = N + (k-N) := by omega
        rw [eq,(raw ⟨k-N,small⟩).2] at mem ⊢
        exact hl _ mem
      obtain ⟨a,b,bnd,kind⟩ := gates (k-n) (by omega)
      have ek : n+(k-n)=k := by omega
      rw [ek] at bnd kind
      have ma := ih a (lt_of_le_of_lt (le_max_left _ _) bnd) (by omega) u v hp hl
      have mb := ih b (lt_of_le_of_lt (le_max_right _ _) bnd) (by omega) u v hp hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at kind
      rcases kind with e|e|e|e <;> rw [e] at mem ⊢
      · exact mem.elim (fun a => Or.inl (ma a)) (fun b => Or.inr (mb b))
      · exact ma mem
      · exact mem
      · exact ⟨ma mem.1,mb mem.2⟩
  have reject (B : Fin N → Bool) (size : Fintype.card {l : Fin N // B l = true} ≤ q) (A : Fin N → Bool)
      (safe : ∀ p, A p = true → ¬∃ l, I p l ∧ B l = true) : (A,B) ∉ W o := by
    intro accepted
    apply neg B size
    exact mono o ho (A,B) _ (fun p hp => decide_eq_true (safe p hp)) (fun _ h => h) accepted
  obtain ⟨T,bound,num,determines⟩ := PEqualNP.Research.L_meta_4289_support N s o W ho gates
  have inputs (p l : Fin N) (edge : I p l) : p.val ∈ T ∧ N+l.val ∈ T := by
    have yes := pos p l edge
    have zline : (one p,zero) ∉ W o := by
      apply reject
      · simp [zero]
      · simp [zero]
    have zpoint : (zero,one l) ∉ W o := by
      apply reject
      · rw [Fintype.card_subtype]
        apply le_trans (Finset.card_le_one.mpr ?_) (by omega : 1 ≤ q)
        intro a ha b hb
        simp [one] at ha hb
        exact ha.trans hb.symm
      · simp [zero]
    constructor
    · by_contra miss
      apply zpoint
      apply (determines (one p,one l) (zero,one l) ?_).mp yes
      intro i h
      by_cases left : i < N
      · rw [(raw ⟨i,left⟩).1]
        have ne : (⟨i,left⟩ : Fin N) ≠ p := fun eq => miss (eq ▸ h)
        simp [one,zero,ne]
      · have lt := bound i h
        have small : i-N < N := by omega
        rw [show i = N+(i-N) by omega,(raw ⟨i-N,small⟩).2]
        rfl
    · by_contra miss
      apply zline
      apply (determines (one p,one l) (one p,zero) ?_).mp yes
      intro i h
      by_cases left : i < N
      · rw [(raw ⟨i,left⟩).1]
        rfl
      · have lt := bound i h
        have small : i-N < N := by omega
        have ne : (⟨i-N,small⟩ : Fin N) ≠ l := by
          intro eq
          have := congrArg Fin.val eq
          apply miss
          change i-N = l.val at this
          rwa [show N+l.val = i by omega]
        rw [show i = N+(i-N) by omega,(raw ⟨i-N,small⟩).2]
        simp [one,zero,ne]
  have sub : Finset.range (N+N) ⊆ T := by
    intro i mem
    have lt := Finset.mem_range.mp mem
    by_cases left : i < N
    · let p : Fin N := ⟨i,left⟩
      obtain ⟨l,h⟩ := rows p
      exact (inputs p l h).1
    · let l : Fin N := ⟨i-N,by omega⟩
      obtain ⟨p,hp⟩ := cols l
      have m := (inputs p l hp).2
      simpa only [l, Nat.add_sub_of_le (by omega : N ≤ i)] using m
  have cap := Finset.card_le_card sub
  rw [Finset.card_range] at cap
  omega

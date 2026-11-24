import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4289_619
  (support : ∀ (N s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))), o < N + N + s →
    (∀ j < s, ∃ a b : ℕ, max a b < N + N + j ∧ W (N+N+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
    ∃ T : Finset ℕ, (∀ i ∈ T, i < N+N) ∧ T.card ≤ s+1 ∧
      ∀ u v : (Fin N → Bool) × (Fin N → Bool), (∀ i ∈ T, u ∈ W i ↔ v ∈ W i) → (u ∈ W o ↔ v ∈ W o))
  (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    199 < q → N = q^2 + q + 1 →
    (∀ l, Fintype.card {p // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
    let n := N+N
    let one := fun (p t : Fin N) => decide (t=p)
    o < n+s →
    (∀ i : Fin N, W i = {v | v.1 i = true} ∧ W (N+i.val) = {v | v.2 i = true}) →
    (∀ j < s, ∃ a b : ℕ, max a b < n+j ∧ W (n+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
    (∀ p l, I p l → (one p,one l) ∈ W o) →
    (∀ B : Fin N → Bool, Fintype.card {l // B l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ B l = true)),B) ∉ W o) →
    (let P := fun k => {p : Fin N | (one p,fun _ => false) ∈ W k}
     ∃ j < s, ∃ a b : ℕ, max a b < n+j ∧ W (n+j) = W a ∩ W b ∧
       (¬P a ⊆ P b) ∧ (¬P b ⊆ P a) ∧
       (∃ p r, p ≠ r ∧ p ∈ P (n+j) ∧ r ∈ P (n+j)) ∧
       ¬∃ c < n+j, ∃ d < n+j, P (n+j) = P c ∪ P d) →
    N*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.true (x12 + x20) ∧ x22 ∈ x19 Bool.true (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.true (x12 + x20) = x19 Bool.true x23 ∪ x19 Bool.true x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hN hc hu s o W n one ho raw gates pos neg ex
  by_cases hi : 199 < q
  · apply large q N I hi hN hc hu s o W ho raw gates pos neg
    let P := fun k => {p : Fin N | (one p,fun _ => false) ∈ W k}
    obtain ⟨j,hj,p,r,ne,hp,hr,fresh⟩ := ex
    change p ∈ P (n+j) at hp
    change r ∈ P (n+j) at hr
    change ¬∃ c < n+j, ∃ d < n+j, P (n+j) = P c ∪ P d at fresh
    obtain ⟨a,b,less,kind⟩ := gates j hj
    have ha := lt_of_le_of_lt (le_max_left _ _) less
    have hb := lt_of_le_of_lt (le_max_right _ _) less
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kind
    rcases kind with e|e|e|e
    · exact (fresh ⟨a,ha,b,hb,by ext t; simp only [P,Set.mem_setOf_eq,Set.mem_union,e]⟩).elim
    · exact (fresh ⟨a,ha,a,ha,by simp [P,e]⟩).elim
    · simp [P,e] at hp
    · have meet : P (n+j) = P a ∩ P b := by ext t; simp [P,e]
      have unequal (c : ℕ) (hc' : c < n+j) : P (n+j) ≠ P c := by
        intro eq
        exact fresh ⟨c,hc',c,hc',by simpa using eq⟩
      have left : ¬P a ⊆ P b := fun sub => unequal a ha (meet.trans (Set.inter_eq_left.mpr sub))
      have right : ¬P b ⊆ P a := fun sub => unequal b hb (meet.trans (Set.inter_eq_right.mpr sub))
      exact ⟨j,hj,a,b,less,e,left,right,⟨p,r,ne,hp,hr⟩,fresh⟩
  classical
  have Nbig : 100 ≤ N := by nlinarith
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
  obtain ⟨T,bound,num,determines⟩ := support N s o W ho gates
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
      let t : Fin N := ⟨if i=0 then 1 else 0,by split <;> omega⟩
      have ne : p ≠ t := by intro e; have a := congrArg Fin.val e; simp [p,t] at a; split at a <;> omega
      obtain ⟨l,h,_⟩ := hu p t ne
      exact (inputs p l h.1).1
    · let l : Fin N := ⟨i-N,by omega⟩
      have nonempty := Fintype.card_pos_iff.mp (show 0 < Fintype.card {p // I p l} by rw [hc]; omega)
      obtain ⟨⟨p,hp⟩⟩ := nonempty
      have m := (inputs p l hp).2
      simpa only [l, Nat.add_sub_of_le (by omega : N ≤ i)] using m
  have cap := Finset.card_le_card sub
  rw [Finset.card_range] at cap
  have h := Nat.mul_le_mul_left N (show q ≤ 199 by omega)
  omega

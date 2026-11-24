import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3091_619
  (single : let E (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit, let u := C.output :: C.gates.flatMap Gate.inputs
    FanInTwo C → C.size = 14 → (∀ i ∈ u, i ≤ 24) → (∀ i < 24, i ∈ u) →
    9 + (C.gates.filter (fun g => g.op.eval [false] && !(g.op.eval [true]))).length + (∑ i ∈ Finset.range 24, (u.count i - 1)) ≤ 14 → 2 ≤ u.count 9 → u.count 1 = 1 →
    (∀ j : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x j]) ≠ E x) →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ E x)
  (saturated : let E (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit, let u := C.output :: C.gates.flatMap Gate.inputs
    Monotone2 C → C.size = 14 → (∀ g ∈ C.gates, g.inputs.length = 2) → (∀ i ∈ u, i < 24) → (∀ i < 24, u.count i = if i ∈ ([1,2,5,8,9] : List ℕ) then 2 else 1) →
    (∀ j : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x j]) ≠ E x) →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ E x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  intro E C fan sz lim live budget nine copy
  classical
  let u := C.output :: C.gates.flatMap Gate.inputs
  let neg (g : Gate) := g.op.eval [false] && !(g.op.eval [true])
  let k := (C.gates.filter neg).length
  let e (i : ℕ) := u.count i - 1
  have allBound (i : ℕ) (hi : i ∈ u) : i ≤ 24 := by
    rcases List.mem_cons.mp hi with rfl|h
    · simpa [sz] using lim.1
    obtain ⟨g,hg,hi⟩ := List.mem_flatMap.mp h
    simpa [sz] using lim.2 g hg i hi
  have alive (i : ℕ) (h : i < 24) : i ∈ u := live i (by simpa [sz] using h)
  have pos (i : ℕ) (h : i < 24) : 0 < u.count i := List.count_pos_iff.mpr (alive i h)
  have B : 9 + k + ∑ i ∈ Finset.range 24, e i ≤ 14 := by simpa only [sz] using budget
  change 2 ≤ u.count 9 at nine
  by_cases cheap : ∃ j ∈ ([1,2,5,8] : List ℕ), u.count j = 1
  · obtain ⟨j,hj,hcheap⟩ := cheap
    have transport (p : Fin 9 → Fin 9) (inv : ∀ i, p (p i) = i)
        (rep : (p 1).val = j) (ep : ∀ x, E (fun i => x (p i)) = E x)
        (keep : ∀ x : Fin 9 → Bool, (x (p 0) || x (p 3)) = (x 0 || x 3)) :
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ E x := by
      let r (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i
      have low (i : Fin 9) : r i.val = (p i).val := by simp [r,i.isLt]
      have high (i : ℕ) (h : 9 ≤ i) : r i = i := by simp [r,Nat.not_lt.mpr h]
      have invol (i : ℕ) : r (r i) = i := by
        by_cases h : i < 9
        · let a : Fin 9 := ⟨i,h⟩
          change r (r a.val) = a.val
          rw [low,low,inv]
        · simp only [high i (Nat.le_of_not_lt h)]
      have inj : Function.Injective r := fun a b h => by simpa only [invol] using congrArg r h
      have small (i : ℕ) (hi : i < 24) : r i < 24 := by
        by_cases h : i < 9
        · have := (p ⟨i,h⟩).isLt; simp [r,h]; omega
        · rw [high _ (by omega)]; exact hi
      let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
      let D : Circuit := ⟨C.gates.map gate,r C.output⟩
      have occ : D.output :: D.gates.flatMap Gate.inputs = u.map r := by
        simp only [D,u,List.map_cons,List.map_flatMap,List.flatMap_map]; rfl
      have count (i : ℕ) : (u.map r).count (r i) = u.count i := by
        exact List.count_map_of_injective u r inj i
      have dk : (D.gates.filter neg).length = k := by
        change ((C.gates.map gate).filter neg).length = _
        simp only [List.filter_map, List.length_map]
        rfl
      have cost : (∑ i ∈ Finset.range 24, ((u.map r).count i - 1)) = ∑ i ∈ Finset.range 24, e i := by
        apply Finset.sum_bij' (fun i _ => r i) (fun i _ => r i)
        · simpa only [Finset.mem_range] using small
        · simpa only [Finset.mem_range] using small
        · exact fun i _ => invol i
        · exact fun i _ => invol i
        · intro i _
          rw [← invol i, count]
          simp only [invol,e]
      let rd (v : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => v.getD i false)
      have run (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
          (ha : 9 ≤ a.length) (rel : ∀ i, a.getD i false = b.getD (r i) false) (i : ℕ) :
          (gs.foldl (fun w g => w ++ [rd w g]) a).getD i false =
          ((gs.map gate).foldl (fun w g => w ++ [rd w g]) b).getD (r i) false := by
        induction gs generalizing a b with
        | nil => exact rel i
        | cons g gs ih =>
          have eqg : rd a g = rd b (gate g) := by
            simp only [rd,gate,List.map_map]
            exact congrArg g.op.eval (List.map_congr_left (fun j _ => rel j))
          apply ih (a ++ [rd a g]) (b ++ [rd b (gate g)]) (by simp [len]) (by simp;omega)
          intro j
          by_cases h : j < a.length
          · have hr : r j < b.length := by
              by_cases h9 : j < 9
              · have := (p ⟨j,h9⟩).isLt; dsimp [r]; split <;> omega
              · rw [high _ (by omega)]; omega
            rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ hr, rel]
          · rw [high j (by omega),List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega),len,eqg]
      have eval (x : Fin 9 → Bool) (v : Bool) :
          C.eval (List.ofFn (fun i => x (p i)) ++ [v]) = D.eval (List.ofFn x ++ [v]) := by
        apply run C.gates _ _ (by simp) (by simp) _ C.output
        intro i
        by_cases hi : i < 9
        · have ri : r i < 9 := by simp [r,hi]
          rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_append _ _ _ _ (by simpa using ri),
            List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using ri)]
          simp only [List.getElem_ofFn,r,dite_eq_left hi]
        · rw [high i (by omega),List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi),
              List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi)]
          simp
      have dfan : FanInTwo D := by
        intro g hg
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
        exact ⟨(fan t ht).1,by simpa [gate] using (fan t ht).2⟩
      have dsz : D.size = 14 := by change (C.gates.map gate).length = 14; rw [List.length_map]; exact sz
      have bounded (i : ℕ) (hi : i ∈ u.map r) : i ≤ 24 := by
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
        have h := allBound a ha
        by_cases lt : a < 24
        · exact Nat.le_of_lt (small _ lt)
        · rw [high a (by omega)]; exact h
      have dlive (i : ℕ) (hi : i < 24) : i ∈ u.map r :=
        List.mem_map.mpr ⟨r i,alive _ (small i hi),invol i⟩
      have cnine := count 9
      rw [high 9 (by decide)] at cnine
      have cone := count (r 1)
      rw [invol 1,show r 1 = j from (low (1 : Fin 9)).trans rep] at cone
      have dcopy (a : Fin 9) : ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x a]) ≠ E x := by
            obtain ⟨y,hy⟩ := copy (p a)
            let x := fun i => y (p i)
            refine ⟨x,?_⟩
            have e' := eval x (x a)
            have flip : (fun i => x (p i)) = y := by funext i; simp [x,inv]
            rw [flip] at e'
            change D.eval (List.ofFn x ++ [x a]) ≠ E x
            rw [← e',show E x = E y from ep y]
            exact hy
      have ans := single D dfan dsz (by rw [occ]; exact bounded) (by rw [occ]; exact dlive)
        (by change 9 + (D.gates.filter neg).length + (∑ i ∈ Finset.range 24, ((D.output :: D.gates.flatMap Gate.inputs).count i - 1)) ≤ 14; rw [occ,cost,dk]; exact B)
        (by rw [occ,cnine]; exact nine) (by rw [occ,cone]; exact hcheap) dcopy
      obtain ⟨x,hx⟩ := ans
      refine ⟨fun i => x (p i),?_⟩
      rw [ep x,keep x,eval x (x 0 || x 3)]; exact hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl
    · let p : Fin 9 → Fin 9 := ![0,1,2,3,4,5,6,7,8]
      apply transport p (by decide) (by decide) (by
        intro x
        change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl)
      intro x
      change (x 0 || x 3) = (x 0 || x 3)
      ac_rfl
    · let p : Fin 9 → Fin 9 := ![3,2,1,0,4,8,7,6,5]
      apply transport p (by decide) (by decide) (by
        intro x
        change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl)
      intro x
      change (x 3 || x 0) = (x 0 || x 3)
      ac_rfl
    · let p : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
      apply transport p (by decide) (by decide) (by
        intro x
        change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl)
      intro x
      change (x 0 || x 3) = (x 0 || x 3)
      ac_rfl
    · let p : Fin 9 → Fin 9 := ![3,8,5,0,4,2,6,7,1]
      apply transport p (by decide) (by decide) (by
        intro x
        change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl)
      intro x
      change (x 3 || x 0) = (x 0 || x 3)
      ac_rfl
  · let S : Finset ℕ := {1,2,5,8,9}
    have sub : S ⊆ Finset.range 24 := by decide
    have unit (i : ℕ) (hi : i ∈ S) : 1 ≤ e i := by
      have pp := pos i (Finset.mem_range.mp (sub hi))
      by_cases h9 : i = 9
      · subst i; dsimp [e]; omega
      · have m : i ∈ ([1,2,5,8] : List ℕ) := by simpa [S,h9] using hi
        have nn : u.count i ≠ 1 := fun h => cheap ⟨i,m,h⟩
        dsimp [e]; omega
    have split := Finset.sum_sdiff (f := e) sub
    have mass : 5 ≤ ∑ i ∈ S, e i := by
      calc
        5 = ∑ _i ∈ S, (1 : ℕ) := by decide
        _ ≤ _ := Finset.sum_le_sum unit
    have rest : ∑ i ∈ Finset.range 24 \ S, e i = 0 := by omega
    have none : k = 0 := by omega
    have prof (i : ℕ) (hi : i < 24) : u.count i = if i ∈ ([1,2,5,8,9] : List ℕ) then 2 else 1 := by
      have pp := pos i hi
      change u.count i = _
      by_cases h : i ∈ S
      · have lm : i ∈ ([1,2,5,8,9] : List ℕ) := by simpa [S] using h
        rw [ite_eq_left lm]
        have four : 4 = ∑ _j ∈ S.erase i, (1 : ℕ) := by
          simp [Finset.card_erase_of_mem h, S]
        have lb : 4 ≤ ∑ j ∈ S.erase i, e j := four ▸ Finset.sum_le_sum (fun j hj => unit j (Finset.mem_of_mem_erase hj))
        have z := Finset.sum_erase_add (s := S) e h
        have ei := unit i h
        have upper : e i ≤ 1 := by omega
        change u.count i - 1 ≤ 1 at upper
        change 1 ≤ u.count i - 1 at ei
        omega
      · have lm : i ∉ ([1,2,5,8,9] : List ℕ) := by simpa [S] using h
        rw [ite_eq_right lm]
        have mem : i ∈ Finset.range 24 \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hi,h⟩
        have upper := Finset.single_le_sum (f := e) (fun j _ => Nat.zero_le (e j)) mem
        rw [rest] at upper
        change u.count i - 1 ≤ 0 at upper
        omega

    let A := Finset.range 24
    have used : A ⊆ u.toFinset := fun i h => List.mem_toFinset.mpr (alive i (Finset.mem_range.mp h))
    have total : ∑ i ∈ A, u.count i = 29 := by
      calc
        _ = ∑ i ∈ A, (if i ∈ ([1,2,5,8,9] : List ℕ) then 2 else 1 : ℕ) :=
          Finset.sum_congr rfl (fun i hi => prof i (Finset.mem_range.mp hi))
        _ = 29 := by decide
    have space (L : Finset ℕ) (inc : L ⊆ u.toFinset) : ∑ i ∈ L, u.count i ≤ u.length := by
      rw [← List.sum_toFinset_count_eq_length u]
      exact Finset.sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => Nat.zero_le _)
    have fill (gs : List Gate) (ok : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length ∧
        ((gs.flatMap Gate.inputs).length = 2 * gs.length → ∀ g ∈ gs, g.inputs.length = 2) := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        obtain ⟨bound,unique⟩ := ih (fun t h => ok t (List.mem_cons_of_mem _ h))
        have small := ok g (by simp)
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        constructor
        · omega
        · intro h t ht
          rcases List.mem_cons.mp ht with rfl|ht
          · omega
          · exact unique (by omega) t ht
    obtain ⟨ub,exactPins⟩ := fill C.gates (fun g hg => (fan g hg).2)
    have lower := space A used
    rw [total] at lower
    have ul : u.length = (C.gates.flatMap Gate.inputs).length + 1 := rfl
    change C.gates.length = 14 at sz
    have tight : u.length = 29 := by omega
    have bounded (i : ℕ) (h : i ∈ u) : i < 24 := by
      by_contra! big
      have outside : i ∉ A := by simpa [A] using big
      have hb := space (insert i A) (Finset.insert_subset (List.mem_toFinset.mpr h) used)
      rw [Finset.sum_insert outside,total,tight] at hb
      have := List.count_pos_iff.mpr h
      omega
    apply saturated C _ sz (exactPins (by omega)) bounded prof copy
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    refine ⟨?_,len⟩
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    rcases op with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have nf : C.gates.filter neg = [] := List.length_eq_zero_iff.mp none
      have hit : g ∈ C.gates.filter neg := List.mem_filter.mpr ⟨hg,by dsimp [neg]; rw [hn]; rfl⟩
      simp [nf] at hit

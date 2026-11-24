import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3394_619
  (posted : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := x1.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]);           x2.eval (x6 ++ [!x6.getD x1.output Bool.false]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size + x2.size)
  (cross : ∀ k ∈ ([2,3,5] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6] ++ [!x k]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (low : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6] ++ [!x 2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let E (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let canon (a b k : Fin 9) := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x a || x b] ++ [!x k]) ≠ E x
  have edge (k : Fin 9) : canon 0 4 k := by
    intro C fan sz
    by_contra! ok
    let P : Circuit := ⟨[],k.val⟩
    have lb := posted P C (by intro g hg; change g ∈ ([] : List Gate) at hg; simp at hg) fan (by
      intro x
      change C.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [!((List.ofFn x ++ [x 0 || x 4]).getD k.val false)]) = E x
      rw [List.getD_append _ _ _ _ (by simpa using k.isLt),List.getD_eq_getElem _ _ (by simpa using k.isLt),List.getElem_ofFn]
      exact ok x)
    change 14 ≤ 0 + C.size at lb
    omega
  have transfer (j a b k : Fin 9) (p : Fin 9 → Fin 9) (pk : p 0 = k)
      (symm : ∀ x : Fin 9 → Bool, E (fun t => x (p t)) = E x)
      (orp : ∀ x : Fin 9 → Bool, (x (p 6) || x (p j)) = if j = 6 then x (p 6) else (x a || x b))
      (base : canon a b k) (C : Circuit) (fan : FanInTwo C) (sz : C.size ≤ 13) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x j]) ≠ E x := by
    let r (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else if i = 9 then 10 else
      if i = 10 then (if j = 6 then (p 6).val else 9) else i
    have hi (i : ℕ) (h : 11 ≤ i) : r i = i := by
      simp [r,show ¬ i < 9 by omega,show i ≠ 9 by omega,show i ≠ 10 by omega]
    have lo (i : ℕ) (h : i < 11) : r i < 11 := by
      dsimp [r]; split
      · rename_i h'; exact lt_trans (p ⟨i,h'⟩).isLt (by decide)
      · split
        · decide
        · split
          · split
            · exact lt_trans (p 6).isLt (by decide)
            · decide
          · exact h
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
    let D : Circuit := ⟨C.gates.map gate,r C.output⟩
    have dfan : FanInTwo D := by
      intro g hg
      obtain ⟨g,mg,rfl⟩ := List.mem_map.mp hg
      exact ⟨(fan g mg).1,by simpa [gate] using (fan g mg).2⟩
    have dsz : D.size ≤ 13 := by change (C.gates.map gate).length ≤ 13; rw [List.length_map]; exact sz
    obtain ⟨x,hx⟩ := base D dfan dsz
    let y := fun t => x (p t)
    let u := List.ofFn y ++ [!y 0] ++ [y 6 || y j]
    let v := List.ofFn x ++ [x a || x b] ++ [!x k]
    have first (z : Fin 9 → Bool) (c d : Bool) (i : Fin 9) :
        (List.ofFn z ++ [c] ++ [d]).getD i.val false = z i := by
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using i.isLt),
        List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
    have rel (i : ℕ) : u.getD i false = v.getD (r i) false := by
      by_cases small : i < 9
      · let t : Fin 9 := ⟨i,small⟩
        change (List.ofFn y ++ [_] ++ [_]).getD t.val false = (List.ofFn x ++ [_] ++ [_]).getD (r i) false
        rw [show r i = (p t).val by simp [r,small,t],first,first]
      by_cases eq9 : i = 9
      · subst i
        change (!x (p 0)) = (!x k)
        rw [pk]
      by_cases eq10 : i = 10
      · subst i
        by_cases h : j = 6
        · have eq : r 10 = (p 6).val := by simp [r,h]
          rw [eq, show v.getD (p 6).val false = x (p 6) from first x _ _ (p 6)]
          change (x (p 6) || x (p j)) = x (p 6)
          simpa only [ite_eq_left h] using orp x
        · rw [show r 10 = 9 by simp [r,h]]
          change (x (p 6) || x (p j)) = (x a || x b)
          simpa only [ite_eq_right h] using orp x
      rw [hi _ (by omega),List.getD_eq_default _ _ (by simp [u]; omega),List.getD_eq_default _ _ (by simp [v]; omega)]
    let rd (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
    have run (gs : List Gate) (s t : List Bool) (hlen : s.length = t.length) (bound : 11 ≤ s.length)
        (agree : ∀ i, s.getD i false = t.getD (r i) false) (i : ℕ) :
        (gs.foldl (fun z g => z ++ [rd z g]) s).getD i false =
        ((gs.map gate).foldl (fun z g => z ++ [rd z g]) t).getD (r i) false := by
      induction gs generalizing s t with
      | nil => exact agree i
      | cons g gs ih =>
        have eqg : rd s g = rd t (gate g) := by
          simp only [rd,gate,List.map_map]
          exact congrArg g.op.eval (List.map_congr_left (fun i _ => agree i))
        apply ih (s ++ [rd s g]) (t ++ [rd t (gate g)]) (by simp [hlen]) (by simp; omega)
        intro n
        by_cases h : n < s.length
        · have hr : r n < t.length := by
            by_cases h' : n < 11
            · have := lo n h'; omega
            · rw [hi _ (by omega)]; omega
          rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ hr, agree]
        · rw [hi n (by omega),List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen,eqg]
    have eqv : C.eval u = D.eval v := run C.gates _ _ (by simp [u,v]) (by simp [u]) rel C.output
    refine ⟨y,?_⟩
    change C.eval u ≠ E y
    rw [eqv,show E y = E x from symm x]
    exact hx
  intro j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · let p : Fin 9 → Fin 9 := ![1,0,5,8,6,2,4,7,3]
    apply transfer 1 0 4 1 p (by decide) _ _ (edge 1)
    · intro x
      change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 4 || x 0) = (x 0 || x 4)
      ac_rfl
  · let p : Fin 9 → Fin 9 := ![2,1,0,5,7,3,6,4,8]
    apply transfer 2 0 6 2 p (by decide) _ _ (cross 2 (by decide))
    · intro x
      change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 6 || x 0) = (x 0 || x 6)
      ac_rfl
  · let p : Fin 9 → Fin 9 := ![3,8,5,0,4,2,6,7,1]
    apply transfer 3 0 6 3 p (by decide) _ _ (cross 3 (by decide))
    · intro x
      change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 6 || x 0) = (x 0 || x 6)
      ac_rfl
  · let p : Fin 9 → Fin 9 := ![5,8,3,2,7,0,6,4,1]
    apply transfer 5 0 6 5 p (by decide) _ _ (cross 5 (by decide))
    · intro x
      change ((x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 8 && x 6) || (x 3 && x 4) || (x 2 && x 1) || (x 0 && x 4) || (x 6 && x 1) || (x 1 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 6 || x 0) = (x 0 || x 6)
      ac_rfl
  · let p : Fin 9 → Fin 9 := ![1,0,5,8,6,2,4,7,3]
    apply transfer 6 0 4 1 p (by decide) _ _ (edge 1)
    · intro x
      change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 4 || x 4) = x 4
      exact Bool.or_self _
  · let p : Fin 9 → Fin 9 := ![2,1,0,5,7,3,6,4,8]
    apply transfer 7 4 6 2 p (by decide) _ _ (low)
    · intro x
      change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 6 || x 4) = (x 4 || x 6)
      ac_rfl
  · let p : Fin 9 → Fin 9 := ![8,3,2,1,6,5,4,7,0]
    apply transfer 8 0 4 8 p (by decide) _ _ (edge 8)
    · intro x
      change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · intro x
      change (x 4 || x 0) = (x 0 || x 4)
      ac_rfl

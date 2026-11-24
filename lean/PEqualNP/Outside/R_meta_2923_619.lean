import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2923_619
  (pair : ∀ p ∈ ([(0, 1), (0, 2), (0, 4), (0, 6), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (4, 6), (6, 7)] : List (Fin 9 × Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 && x 3]) ++ [x p.1 && x p.2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (triple : ∀ k ∈ ([1, 4, 6] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 && x 3]) ++ [x k && (x 0 && x 3)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[], [(0 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (1 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(9 : Fin (11 : ℕ))], [(10 : Fin (11 : ℕ))]],     PEqualNP.MetaComplexity.FanInTwo x1 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  let edge (x : Fin 9 → Bool) := ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let wire (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 3]
  have wlen (x) : (wire x).length = 10 := by simp [wire]
  let fail (h : (Fin 9 → Bool) → Bool) := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval (wire x ++ [h x]) ≠ edge x
  let lit (i : Nat) (x : Fin 9 → Bool) := (wire x).getD i false
  let aux (x : Fin 9 → Bool) := x 0 && x 1
  have base : fail aux := pair (0,1) (by decide)
  have existingInput (j : Nat) (hj : j < 10) : fail (lit j) := by
    intro C ok sz
    let f (i : Nat) := if i = 10 then j else i
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
    let D : Circuit := ⟨C.gates.map gate,f C.output⟩
    have okD : FanInTwo D := by
      intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      exact ⟨(ok v hv).1,by simpa [gate] using (ok v hv).2⟩
    have szD : D.size ≤ 13 := by
      change (C.gates.map gate).length ≤ 13
      rw [List.length_map]; exact sz
    obtain ⟨x,hx⟩ := base D okD szD
    refine ⟨x,?_⟩
    let rd (v : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => v.getD i false)
    have snoc (v : List Bool) (b : Bool) (i : Nat) :
        (v ++ [b]).getD i false = if i = v.length then b else v.getD i false := by
      by_cases hi : i < v.length
      · simp [List.getD,List.getElem?_append,hi, Nat.ne_of_lt hi]
      · by_cases he : i = v.length
        · subst i; simp [List.getD]
        · have ho : (v ++ [b]).length ≤ i := by simp; omega
          simp [List.getD, List.getElem?_eq_none ho, List.getElem?_eq_none (Nat.le_of_not_lt hi),he]
    have ext (gs : List Gate) (u v : List Bool) (len : u.length = v.length)
        (hl : 11 ≤ u.length) (rel : ∀ i, u.getD i false = v.getD (f i) false) (i : Nat) :
        (gs.foldl (fun a g => a ++ [rd a g]) u).getD i false =
        ((gs.map gate).foldl (fun a g => a ++ [rd a g]) v).getD (f i) false := by
      induction gs generalizing u v with
      | nil => exact rel i
      | cons g gs ih =>
        apply ih (u ++ [rd u g]) (v ++ [rd v (gate g)]) (by simp [len]) (by simp; omega)
        intro a
        have val : rd u g = rd v (gate g) := by
          simp only [rd,gate,List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => rel i)
        rw [snoc,snoc]
        by_cases ha : a = u.length
        · have hf : f a = v.length := by unfold f; rw [ite_eq_right (show a ≠ 10 by omega)]; omega
          rw [ite_eq_left ha,ite_eq_left hf,val]
        · have hf : f a ≠ v.length := by dsimp [f]; split <;> omega
          rw [ite_eq_right ha,ite_eq_right hf,rel a]
    have rel (i : Nat) : (wire x ++ [lit j x]).getD i false = (wire x ++ [aux x]).getD (f i) false := by
      rw [snoc (wire x) (lit j x) i,snoc (wire x) (aux x) (f i),wlen]
      by_cases hi : i = 10
      · simp [f,hi,lit,show j ≠ 10 by omega]
      · simp [f,hi]
    have same := ext C.gates _ _ (by simp) (by simp [wlen]) rel C.output
    exact fun he => hx (same.symm.trans he)
  have constant (b : Bool) : fail (fun _ => b) := by
    intro C ok sz
    by_cases hout : C.output = 10
    · let x : Fin 9 → Bool := fun _ => !b
      refine ⟨x,?_⟩
      let rd (v : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => v.getD i false)
      have keep (gs : List Gate) (v : List Bool) (i : Nat) (hi : i < v.length) :
          (gs.foldl (fun a g => a ++ [rd a g]) v).getD i false = v.getD i false := by
        induction gs generalizing v with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih _ (by simp; omega)]
          exact List.getD_append _ _ _ _ hi
      change (C.gates.foldl (fun a g => a ++ [rd a g]) (wire x ++ [b])).getD C.output false ≠ edge x
      rw [hout, keep _ _ _ (by simp [wlen]), List.getD_append_right _ _ _ _ (by rw [wlen]), wlen]
      cases b <;> decide
    let rd (v : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => v.getD i false)
    classical
    let K (c : Bool) : Gate := if c then ⟨.and,[]⟩ else ⟨.or,[]⟩
    let gate (g : Gate) : Gate :=
      if 10 ∈ g.inputs then
        if g.op = .and then (if b then ⟨.and,g.inputs.filter (· != 10)⟩ else K false)
        else if g.op = .or then (if b then K true else ⟨.or,g.inputs.filter (· != 10)⟩)
        else if g.inputs.head? = some 10 then K (!b) else g
      else g
    let D : Circuit := ⟨C.gates.map gate,C.output⟩
    have legal : FanInTwo D := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
      obtain ⟨op,len⟩ := ok g hg
      change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
      by_cases h : 10 ∈ g.inputs
      · rcases op with h'|h'|h' <;> cases b <;> simp [gate,h,h',K] <;>
          first | exact le_trans (List.length_filter_le ..) len |
            (split <;> simp_all)
      · simpa only [gate,ite_eq_right h] using ok g hg
    have size : D.size ≤ 13 := by change (C.gates.map gate).length ≤ 13; rwa [List.length_map]
    obtain ⟨x,hx⟩ := base D legal size
    refine ⟨x,fun he => hx (Eq.trans (b := C.eval (wire x ++ [b])) ?_ he)⟩
    have step (g : Gate) (hg : g ∈ C.gates) (u v : List Bool) (hb : u.getD 10 false = b)
        (hr : ∀ i, i ≠ 10 → u.getD i false = v.getD i false) : rd u g = rd v (gate g) := by
      have hb2 : u[10]?.getD false = b := hb
      have hr2 (i : Nat) (h : i ≠ 10) : u[i]?.getD false = v[i]?.getD false := hr i h
      by_cases has : 10 ∈ g.inputs
      · obtain ⟨hop,len⟩ := ok g hg
        change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
        have ea (l : List Bool) : GateOp.and.eval l = l.all id := rfl
        have eo (l : List Bool) : GateOp.or.eval l = l.any id := rfl
        have en (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
        cases gi : g.inputs with
        | nil => simp [gi] at has
        | cons a tail =>
          cases tail with
          | nil =>
            have ha : a = 10 := by simpa [gi, eq_comm] using has
            subst a
            rcases hop with hop|hop|hop <;> cases b <;> simp [rd,gate,hop,K,gi,ea,eo,en,hb2]
          | cons c rest =>
            have emp : rest = [] := by rw [gi] at len; simpa using len
            subst rest
            by_cases ha : a = 10 <;> by_cases hc : c = 10 <;>
              first | (solve | exfalso; simp [gi,Ne.symm ha,Ne.symm hc] at has) |
                (rcases hop with hop|hop|hop <;> cases b <;>
                  simp [rd,gate,hop,gi,K,ea,eo,en,ha,hc,hb2,hr2])
      · simp only [gate,ite_eq_right has,rd]
        congr 1
        exact List.map_congr_left (fun i hi => hr i (fun e => has (e ▸ hi)))
    have run (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ C.gates) (u v : List Bool)
        (len : u.length = v.length) (hl : 10 < u.length) (hb : u.getD 10 false = b)
        (hr : ∀ i, i ≠ 10 → u.getD i false = v.getD i false) (i : Nat) (hi : i ≠ 10) :
        (gs.foldl (fun a g => a ++ [rd a g]) u).getD i false =
        ((gs.map gate).foldl (fun a g => a ++ [rd a g]) v).getD i false := by
      induction gs generalizing u v with
      | nil => exact hr i hi
      | cons g gs ih =>
        have eqg := step g (sub g (by simp)) u v hb hr
        apply ih (fun t ht => sub t (List.mem_cons_of_mem _ ht)) (u ++ [rd u g]) (v ++ [rd v (gate g)]) (by simp [len]) (by simp; omega)
        · rw [List.getD_append _ _ _ _ hl]; exact hb
        · intro j hj
          by_cases h : j < u.length
          · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by omega),hr _ hj]
          · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len,eqg]
    apply Eq.symm
    apply run C.gates (fun _ h => h) (wire x ++ [b]) (wire x ++ [aux x]) (by simp) (by simp [wlen]) _ _ C.output hout
    · rw [List.getD_append_right _ _ _ _ (by rw [wlen]), wlen]; rfl
    · intro i hi
      by_cases h : i < (wire x).length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
      · have q : (wire x ++ [b]).length ≤ i := by simp [wlen] at h ⊢; omega
        rw [List.getD_eq_default _ _ q,List.getD_eq_default _ _ (by simpa using q)]
  have outside (x) : lit 10 x = false := List.getD_eq_default _ _ (by rw [wlen])
  intro C pins hp ok good
  by_contra! small
  have no (h : (Fin 9 → Bool) → Bool) (hh : fail h) (eqn : ∀ x, GateOp.and.eval (pins.map fun i => lit i.val x) = h x) : False := by
    obtain ⟨x,hx⟩ := hh C ok (by omega)
    apply hx
    rw [← eqn x]
    exact good x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply no _ (constant true)
    intro x
    rfl
  · apply no _ (existingInput 0 (by decide))
    intro x
    change (lit 0 x && true) = _; simp
  · apply no _ (pair (0,1) (by decide))
    intro x
    change (lit 0 x && (lit 1 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (0,2) (by decide))
    intro x
    change (lit 0 x && (lit 2 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (0,4) (by decide))
    intro x
    change (lit 0 x && (lit 4 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (0,6) (by decide))
    intro x
    change (lit 0 x && (lit 6 x && true)) = _; simp [lit, wire]
  · apply no _ (existingInput 1 (by decide))
    intro x
    change (lit 1 x && true) = _; simp
  · apply no _ (pair (1,2) (by decide))
    intro x
    change (lit 1 x && (lit 2 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (1,4) (by decide))
    intro x
    change (lit 1 x && (lit 4 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (1,5) (by decide))
    intro x
    change (lit 1 x && (lit 5 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (1,6) (by decide))
    intro x
    change (lit 1 x && (lit 6 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (1,7) (by decide))
    intro x
    change (lit 1 x && (lit 7 x && true)) = _; simp [lit, wire]
  · apply no _ (pair (1,8) (by decide))
    intro x
    change (lit 1 x && (lit 8 x && true)) = _; simp [lit, wire]
  · apply no _ (triple 1 (by decide))
    intro x
    change (lit 1 x && (lit 9 x && true)) = _; simp [lit, wire]
  · apply no _ (existingInput 4 (by decide))
    intro x
    change (lit 4 x && true) = _; simp
  · apply no _ (pair (4,6) (by decide))
    intro x
    change (lit 4 x && (lit 6 x && true)) = _; simp [lit, wire]
  · apply no _ (triple 4 (by decide))
    intro x
    change (lit 4 x && (lit 9 x && true)) = _; simp [lit, wire]
  · apply no _ (existingInput 6 (by decide))
    intro x
    change (lit 6 x && true) = _; simp
  · apply no _ (pair (6,7) (by decide))
    intro x
    change (lit 6 x && (lit 7 x && true)) = _; simp [lit, wire]
  · apply no _ (triple 6 (by decide))
    intro x
    change (lit 6 x && (lit 9 x && true)) = _; simp [lit, wire]
  · apply no _ (existingInput 9 (by decide))
    intro x
    change (lit 9 x && true) = _; simp
  · apply no _ (constant false)
    intro x
    change (lit 10 x && true) = false; rw [outside]; rfl

import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1936_691
  (fixedBit : ∀ b : Bool, ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!(x 0)]) ++ [b]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (distinctPair : ∀ a b : Fin 10, a < b → ¬ (a = 0 ∧ b = 9) → ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, let w := (List.ofFn x ++ [!(x 0)]); C.eval (w ++ [w.getD a false && w.getD b false]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) := ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let wire (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 0)]
  have wlen (x) : (wire x).length = 10 := by simp [wire]
  let fail (h : (Fin 9 → Bool) → Bool) := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval (wire x ++ [h x]) ≠ edge x
  let lit (i : Nat) (x : Fin 9 → Bool) := (wire x).getD i false
  have constant (b : Bool) : fail (fun _ => b) := fixedBit b
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
    obtain ⟨x,hx⟩ := fixedBit true D okD szD
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
    have rel (i : Nat) : (wire x ++ [lit j x]).getD i false = (wire x ++ [true]).getD (f i) false := by
      rw [snoc (wire x) (lit j x) i,snoc (wire x) true (f i),wlen]
      by_cases hi : i = 10
      · simp [f,hi,lit,show j ≠ 10 by omega]
      · simp [f,hi]
    have same := ext C.gates _ _ (by simp) (by simp [wlen]) rel C.output
    exact fun he => hx (same.symm.trans he)
  have outside (i : Nat) (hi : 10 ≤ i) (x) : lit i x = false := by
    have bound : (wire x).length ≤ i := by simpa only [wlen] using hi
    simp only [lit,List.getD_eq_getElem?_getD,List.getElem?_eq_none bound,Option.getD_none]
  have unary (i : Nat) : fail (lit i) := by
    by_cases hi : i < 10
    · exact existingInput i hi
    · simpa only [show lit i = (fun _ => false) from funext (outside i (Nat.le_of_not_lt hi))] using constant false
  have andPair (a b : Nat) (lt : a < b) : fail (fun x => lit a x && lit b x) := by
    by_cases hi : b < 10
    · by_cases opp : a = 0 ∧ b = 9
      · obtain ⟨rfl,rfl⟩ := opp
        have neg (x : Fin 9 → Bool) : (lit 0 x && lit 9 x) = false := by simp [lit,wire]
        simpa only [show (fun x => lit 0 x && lit 9 x) = (fun _ => false) from funext neg] using constant false
      · exact distinctPair ⟨a,by omega⟩ ⟨b,hi⟩ lt (by simpa [Fin.ext_iff] using opp)
    · have eq : (fun x => lit a x && lit b x) = (fun _ => false) := by funext x; simp [outside b (Nat.le_of_not_lt hi)]
      rw [eq]; exact constant false
  intro pins hp
  change fail (fun x => GateOp.and.eval (pins.map fun i => lit i x))
  cases pins with
  | nil => exact constant true
  | cons a tail =>
    cases tail with
    | nil => change fail (fun x => lit a x && true)
             simpa using unary a
    | cons b rest =>
      have eof : rest = [] := by cases rest <;> simp_all
      subst rest
      change fail (fun x => lit a x && (lit b x && true))
      rcases Nat.lt_trichotomy a b with lt|eq|gt
      · simpa using andPair a b lt
      · subst b; simpa using unary a
      · simpa [Bool.and_comm] using andPair b a gt

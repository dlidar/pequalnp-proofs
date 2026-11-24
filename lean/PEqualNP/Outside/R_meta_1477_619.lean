import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1477_619
  (compile : ∀ (A B : Type) (n : ℕ) (P : A → Fin n → Bool) (N : B → Fin n → Bool) (C : Circuit), Monotone2 C → 
    let step := fun (F : Set (Set A × Set B)) (r : Set A × Set B) =>
      F ∪ {t | t=r ∧ ∃ u ∈ F, ∃ v ∈ F, t.1 ×ˢ t.2 ⊆ (u.1 ×ˢ u.2) ∪ (v.1 ×ˢ v.2)}
    let F : Set (Set A × Set B) := {(∅,Set.univ)} ∪
      Set.range (fun i : Fin n => ({a | P a i = true},{b | N b i = false}))
    (∀ a, C.eval (List.ofFn (P a)) = true) → (∀ b, C.eval (List.ofFn (N b)) = false) →
    ∃ Q : List (Set A × Set B), Q.length = C.size ∧ (Set.univ,Set.univ) ∈ Q.foldl step F)
  (obstruction : let adj : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (point line : Fin (42 : ℕ)) => ↑point < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑line ∧ (↑line + (21 : ℕ) - ↑point) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
    let Edge : Type := { e : Fin (42 : ℕ) × Fin (42 : ℕ) // adj e.1 e.2 };
    let Mask : Type := Finset (Fin (21 : ℕ));
    have ends : Edge → Fin (42 : ℕ) × Fin (42 : ℕ) := Subtype.val;
    let n : ℕ := (42 : ℕ);
    ∀ (positive : Edge → Fin (42 : ℕ) → Bool) (negative : Mask → Fin (42 : ℕ) → Bool),   (∀ (edge : Edge) (i : Fin (42 : ℕ)), positive edge i = Bool.true ↔ i = (ends edge).1 ∨ i = (ends edge).2) →
      (∀ (s : Mask) (i : Fin (42 : ℕ)), negative s i = Bool.true ↔ (∃ point ∈ s, Fin.castAdd (21 : ℕ) point = i) ∨ (21 : ℕ) ≤ ↑i ∧ ∀ point ∈ s, ¬adj (Fin.castAdd (21 : ℕ) point) i) →       
      have extend : Set (Set Edge × Set Mask) → Set Edge × Set Mask → Set (Set Edge × Set Mask) := fun (family : Set (Set Edge × Set Mask)) (candidate : Set Edge × Set Mask) => family ∪ {r : Set Edge × Set Mask | r = candidate ∧ ∃ u ∈ family, ∃ v ∈ family, r.1 ×ˢ r.2 ⊆ u.1 ×ˢ u.2 ∪ v.1 ×ˢ v.2};
    have initial : Set (Set Edge × Set Mask) := {(∅, Set.univ)} ∪ Set.range fun (i : Fin n) => ({input : Edge | positive input i = Bool.true}, {input : Mask | negative input i = Bool.false});
    ∀ (steps : List (Set Edge × Set Mask)), (Set.univ, Set.univ) ∈ List.foldl extend initial steps → (125 : ℕ) ≤ steps.length) :
  ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C,hm,hs,h⟩
  let adj := fun (u v : Fin 42) => (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ))
  let A := {e : Fin 42 × Fin 42 // adj e.1 e.2}
  let B := Finset (Fin 21)
  let n := 42
    
  let P := fun (e : A) (i : Fin 42) => decide (i=e.val.1 ∨ i=e.val.2)
  let N := fun (s : Finset (Fin 21)) (i : Fin 42) => decide ((∃ p ∈ s, Fin.castAdd 21 p = i) ∨ (21 ≤ i.val ∧ ∀ p ∈ s, ¬ adj (Fin.castAdd 21 p) i))
  have table : ∀ u v : Fin 42, (u.val,v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ↔ adj u v := by decide +kernel
  have pos (e : A) : C.eval (List.ofFn (P e)) = true :=
    (h _).mpr ⟨_,_,(table _ _).mpr e.property,by simp [P],by simp [P]⟩
  have neg (s : B) : C.eval (List.ofFn (N s)) = false := by
    cases hv : C.eval (List.ofFn (N s)) with
    | false => rfl
    | true =>
      obtain ⟨u,v,inc,hu,hv'⟩ := (h _).mp hv
      have hadj := (table _ _).mp inc
      simp only [N,decide_eq_true_eq] at hu hv'
      rcases hu with ⟨p,hp,hpu⟩ | hu
      · rcases hv' with ⟨q,hq,hqv⟩ | ⟨_,avoid⟩
        · exact False.elim ((Nat.not_le_of_gt q.isLt) (show 21 ≤ q.val by simpa only [← hqv,Fin.val_castAdd] using hadj.2.1))
        · have eq : Fin.castAdd 21 p = u := hpu
          exact False.elim ((avoid p hp) (eq ▸ hadj))
      · exact False.elim ((Nat.not_le_of_gt hadj.1) hu.1)
  obtain ⟨Q,len,win⟩ := compile A B 42 P N C hm pos neg
  have lb := obstruction P N (fun e i => by simp only [P,decide_eq_true_eq]) (fun s i => by simp only [N,adj,decide_eq_true_eq]) Q win
  exact (Nat.not_succ_le_self 124) (((len ▸ lb) : 125 ≤ C.size).trans hs)

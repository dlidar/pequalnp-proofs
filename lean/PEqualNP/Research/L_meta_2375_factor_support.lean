import PEqualNP.Defs

namespace PEqualNP.Research.PetersenFactorSupport

abbrev Input := Fin 10 → Bool

def edge (x : Input) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def pin (i : Fin 10) (x : Input) : Input := fun k => if k = i then true else x k

def ignores (g : Input → Bool) (i : Fin 10) : Prop := ∀ x, g (pin i x) = g x

def covers (g : Input → Bool) : Prop := ∀ x, edge x = true → g x = true

def projected (i : Fin 10) (x : Input) := edge x || edge (pin i x)

theorem projected_ignores (i) : ignores (projected i) i := by
  intro x
  have h : pin i (pin i x) = pin i x := by funext k; simp [pin]
  simp only [projected, h, Bool.or_self]
  cases e : edge x with
  | false => simp
  | true =>
    have mono : ∀ k, x k = true → pin i x k = true := by intro k hk; simp [pin, hk]
    simp only [edge, Bool.or_eq_true, Bool.and_eq_true] at e ⊢
    aesop

theorem projected_covers (i) : covers (projected i) := by intro x hx; simp [projected, hx]

def input (m : Fin 1024) : Input := fun k => m.val.testBit k.val

def independent : List (Fin 1024) := [0, 1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 32, 34, 36, 40, 42, 48, 50, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 512, 513, 514, 516, 517, 520, 521, 522, 544, 546, 548, 552, 554, 768, 769, 770, 772, 773]

theorem independent_exact : independent = (List.finRange 1024).filter (fun m => !(edge (input m))) := by decide +kernel

def forced (i j : Fin 10) := independent.filter (fun m =>
  edge (pin i (input m)) && edge (pin j (input m)))

theorem forced_spec (i j : Fin 10) (m : Fin 1024) :
    m ∈ forced i j ↔ edge (input m) = false ∧ edge (pin i (input m)) = true ∧ edge (pin j (input m)) = true := by
  simp [forced, independent_exact, List.mem_filter, and_assoc, and_left_comm, and_comm]

theorem forced_error (a b : Input → Bool) (i j : Fin 10) (ha : covers a) (hb : covers b)
    (hi : ignores a i) (hj : ignores b j) (m : Fin 1024) (hm : m ∈ forced i j) :
    edge (input m) = false ∧ a (input m) = true ∧ b (input m) = true := by
  obtain ⟨he, h₁, h₂⟩ := (forced_spec i j m).mp hm
  exact ⟨he, hi _ ▸ ha _ h₁, hj _ ▸ hb _ h₂⟩

theorem sharp (i j : Fin 10) (m : Fin 1024) :
    m ∈ forced i j ↔ edge (input m) = false ∧ projected i (input m) = true ∧ projected j (input m) = true := by
  rw [forced_spec]
  cases h : edge (input m) <;> simp [projected,h]

def expected (i j : Fin 10) := if i = j then 40 else
  if edge (fun k => decide (k = i ∨ k = j)) then 13 else 24

private theorem row0 : ∀ j : Fin 10, (forced 0 j).length = expected 0 j := by decide +kernel
private theorem row1 : ∀ j : Fin 10, (forced 1 j).length = expected 1 j := by decide +kernel
private theorem row2 : ∀ j : Fin 10, (forced 2 j).length = expected 2 j := by decide +kernel
private theorem row3 : ∀ j : Fin 10, (forced 3 j).length = expected 3 j := by decide +kernel
private theorem row4 : ∀ j : Fin 10, (forced 4 j).length = expected 4 j := by decide +kernel
private theorem row5 : ∀ j : Fin 10, (forced 5 j).length = expected 5 j := by decide +kernel
private theorem row6 : ∀ j : Fin 10, (forced 6 j).length = expected 6 j := by decide +kernel
private theorem row7 : ∀ j : Fin 10, (forced 7 j).length = expected 7 j := by decide +kernel
private theorem row8 : ∀ j : Fin 10, (forced 8 j).length = expected 8 j := by decide +kernel
private theorem row9 : ∀ j : Fin 10, (forced 9 j).length = expected 9 j := by decide +kernel

theorem count_forced (i j : Fin 10) : (forced i j).length = expected i j := by
  fin_cases i <;> first | exact row0 j | exact row1 j | exact row2 j | exact row3 j | exact row4 j | exact row5 j | exact row6 j | exact row7 j | exact row8 j | exact row9 j

theorem full_support (a b : Input → Bool) (hex : ∀ x, (a x && b x) = edge x) :
    (∀ i, ¬ ignores a i) ∨ (∀ j, ¬ ignores b j) := by
  by_contra! h
  obtain ⟨⟨i,hi⟩, ⟨j,hj⟩⟩ := h
  have pos : ∀ x, edge x = true → a x = true ∧ b x = true := by
    intro x hx; exact Bool.and_eq_true_iff.mp ((hex x).trans hx)
  have hn : forced i j ≠ [] := by
    intro he
    have hk := count_forced i j
    rw [he] at hk
    simp only [List.length_nil, expected] at hk
    split at hk
    · omega
    · split at hk <;> omega
  obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil _ hn
  obtain ⟨he,ha,hb⟩ := forced_error a b i j (fun x hx => (pos x hx).1) (fun x hx => (pos x hx).2) hi hj m hm
  have := hex (input m)
  simp [he,ha,hb] at this

theorem other_factor_on_cone (a b : Input → Bool) (i : Fin 10) (hi : ignores a i)
    (hex : ∀ x, (a x && b x) = edge x) (x : Input) (hx : edge (pin i x) = true) :
    b x = edge x := by
  have h := (Bool.and_eq_true_iff.mp ((hex (pin i x)).trans hx)).1
  rw [hi] at h
  simpa [h] using hex x

theorem forced_flip (a b : Input → Bool) (i j : Fin 10) (hi : ignores a i)
    (hex : ∀ x, (a x && b x) = edge x) (m : Fin 1024) (hm : m ∈ forced i j) :
    b (input m) = false ∧ b (pin j (input m)) = true := by
  obtain ⟨hn, h₁, h₂⟩ := (forced_spec i j m).mp hm
  exact ⟨(other_factor_on_cone a b i hi hex _ h₁).trans hn,
         (Bool.and_eq_true_iff.mp ((hex _).trans h₂)).2⟩

theorem flips_per_omission : ∀ i : Fin 10, ((List.finRange 10).map (expected i)).sum = 223 := by decide +kernel

theorem total_forced_flips (i : Fin 10) :
    ((List.finRange 10).map (fun j => (forced i j).length)).sum = 223 := by
  simpa only [count_forced] using flips_per_omission i

theorem omitted_coordinates_case : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ i, ignores (fun x => x9 x x3) i) → (∃ j, ignores (fun x => x9 x x4) j) → (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro gate c u v _ _ _
  dsimp only
  intro ⟨i,hi⟩ ⟨j,hj⟩ _ _ hpos
  have hn : forced i j ≠ [] := by
    intro he
    have hk := count_forced i j
    simp only [he, List.length_nil, expected] at hk
    split at hk
    · omega
    · split at hk <;> omega
  obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil _ hn
  exact ⟨input m, forced_error _ _ i j (fun x hx => (hpos x hx).1)
    (fun x hx => (hpos x hx).2) hi hj m hm⟩

end PEqualNP.Research.PetersenFactorSupport

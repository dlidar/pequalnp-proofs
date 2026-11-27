import Mass
namespace SpinMass
open Finset
theorem raw_pos : ∀ z, 0 < raw z := by decide
theorem raw_le : ∀ z, raw z ≤ 4 := by decide
theorem factor_pos : ∀ z w, 0 < factor z w := by decide
theorem factor_le : ∀ z w, factor z w ≤ 5 := by decide
theorem tag_pos {t : ℕ} (g : Option (Pair t)) (p : Mask t) : 0 < tag g p := by
  cases g with
  | none => exact (by decide : 0 < 4)
  | some e => exact factor_pos _ _
theorem tag_le {t : ℕ} (g : Option (Pair t)) (p : Mask t) : tag g p ≤ 5 := by
  cases g with
  | none => exact (by decide : 4 ≤ 5)
  | some e => exact factor_le _ _
theorem rawprod_pos {t : ℕ} (p : Mask t) : 0 < ∏ i, raw (p i) :=
  Finset.prod_pos (fun i _ => raw_pos _)
theorem obs_pos {t : ℕ} (g : Option (Pair t)) (p : Mask t) : 0 < obs g p := by
  have := mass_identity g p
  have h := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (rawprod_pos p)) (tag_pos g p)
  omega
theorem obs_le {t : ℕ} (g : Option (Pair t)) (p : Mask t) : obs g p ≤ 2^(2*t+2) := by
  have h₁ : (∏ i, raw (p i)) ≤ 4^t := by
    simpa using (Finset.prod_le_prod' (s := (univ : Finset (Fin t))) (g := fun _ => 4) (fun i _ => raw_le (p i)))
  have h₂ := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h₁) (tag_le g p)
  rw [← mass_identity] at h₂
  rw [pow_add, pow_mul]
  norm_num at *
  omega
def reading {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) := ∏ l, obs (G l) p
theorem reading_bound {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) :
    reading G p < 2^(k*(2*t+2)+1) := by
  have h : reading G p ≤ (2^(2*t+2))^k := by
    simpa [reading] using (Finset.prod_le_prod' (s := (univ : Finset (Fin k))) (g := fun _ => 2^(2*t+2)) (fun l _ => obs_le (G l) p))
  rw [← pow_mul,Nat.mul_comm] at h
  rw [pow_succ]
  have : 0 < 2^(k*(2*t+2)) := by positivity
  omega

theorem val_raw {q : ℕ} (hq : q = 3 ∨ q = 5) (z : Fin 3) : (raw z).factorization q = 0 := by
  rcases hq with rfl | rfl <;> fin_cases z <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide

theorem val_tag {t q : ℕ} (hq : q = 3 ∨ q = 5) (g : Option (Pair t)) (p : Mask t) :
    (tag g p).factorization q = if tag g p = q then 1 else 0 := by
  have aux : ∀ q z w, (q = 3 ∨ q = 5) → (factor z w).factorization q = if factor z w = q then 1 else 0 := by
    intro q z w h; rcases h with rfl | rfl <;> fin_cases z <;> fin_cases w <;> first | exact Nat.Prime.factorization_self (by decide : Nat.Prime 3) | exact Nat.Prime.factorization_self (by decide : Nat.Prime 5) | exact Nat.factorization_eq_zero_of_not_dvd (by decide)
  cases g with
  | none => rcases hq with rfl | rfl <;> exact Nat.factorization_eq_zero_of_not_dvd (n := 4) (by decide)
  | some e => exact aux q _ _ hq

theorem val_obs {t q : ℕ} (hq : q = 3 ∨ q = 5) (g : Option (Pair t)) (p : Mask t) :
    (obs g p).factorization q = if tag g p = q then 1 else 0 := by
  have h := congrArg (fun n : ℕ => n.factorization q) (mass_identity g p)
  have h2 : (2:ℕ).factorization q = 0 := by rcases hq with rfl | rfl <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide
  have h4 : (4:ℕ).factorization q = 0 := by rcases hq with rfl | rfl <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide
  simp only [Nat.factorization_mul (by decide : 4 ≠ 0) (obs_pos g p).ne',
    Nat.factorization_mul (Nat.mul_ne_zero (by decide : 2 ≠ 0) (rawprod_pos p).ne') (tag_pos g p).ne',
    Nat.factorization_mul (by decide : 2 ≠ 0) (rawprod_pos p).ne',
    Nat.factorization_prod (fun i _ => (raw_pos (p i)).ne'),
    Finsupp.add_apply, Finsupp.finsetSum_apply, val_raw hq, Finset.sum_const_zero,
    h2,h4,zero_add, val_tag hq] at h
  exact h

theorem val_reading {t k q : ℕ} (hq : q = 3 ∨ q = 5)
    (G : Fin k → Option (Pair t)) (p : Mask t) :
    (reading G p).factorization q = (univ.filter (fun l => tag (G l) p = q)).card := by
  unfold reading
  rw [Nat.factorization_prod (fun l _ => (obs_pos (G l) p).ne'), Finsupp.finsetSum_apply]
  simp_rw [val_obs hq]
  exact Finset.sum_boole _ _

def sign (z : Fin 3) : ℤ := if z = 0 then 0 else if z = 1 then -1 else 1
def edgeSign {t : ℕ} (g : Option (Pair t)) (p : Mask t) : ℤ :=
  g.elim 0 (fun e => sign (p e.val.1) * sign (p e.val.2))
theorem sign_table {t : ℕ} (g : Option (Pair t)) (p : Mask t) :
    edgeSign g p = (if tag g p = 5 then 1 else 0) - (if tag g p = 3 then 1 else 0) := by
  cases g with
  | none => rfl
  | some e =>
    exact (by decide : ∀ z w, sign z * sign w = (if factor z w = 5 then 1 else 0) - (if factor z w = 3 then 1 else 0)) _ _
theorem signed_reading {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) :
    (∑ l, edgeSign (G l) p) = ((reading G p).factorization 5 : ℤ) - ((reading G p).factorization 3 : ℤ) := by
  simp_rw [sign_table, Finset.sum_sub_distrib]
  rw [val_reading (Or.inr rfl),val_reading (Or.inl rfl),Finset.sum_boole,Finset.sum_boole]
end SpinMass

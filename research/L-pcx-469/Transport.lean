import Project
namespace SpinHash
open Finset SpinMass
variable {t b k H : ℕ}

def common {n : ℕ} (m : Mask n) : ℕ := 2 * ∏ i, raw (m i)
def pattern {n : ℕ} (M : Model n k) (m : Mask n) := ∏ l, tag (M l) m
theorem common_pos {n : ℕ} (m : Mask n) : 0 < common m := Nat.mul_pos (by decide) (rawprod_pos m)
theorem scaled {n : ℕ} (M : Model n k) (m : Mask n) :
    4^k * reading M m = (common m)^k * pattern M m := by
  have h := Finset.prod_congr (s₁ := (univ : Finset (Fin k))) rfl (fun l _ => mass_identity (M l) m)
  simpa [Finset.prod_mul_distrib,reading,pattern,common] using h

def prediction (c : Label t b) (M : Model b k) (m : Mask b) :=
  (common (m ∘ c))^k * pattern M m
theorem prediction_exact {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (m : Mask b) :
    prediction c (fun l => project c (G l)) m = 4^k * reading G (m ∘ c) := by
  rw [scaled]; unfold prediction pattern; simp_rw [tag_project hc]

theorem prediction_eq_iff (c : Label t b) (M N : Model b k) (m : Mask b) :
    prediction c M m = prediction c N m ↔ reading M m = reading N m := by
  have hc := Nat.pow_pos (common_pos m) (n := k)
  have hc' := Nat.pow_pos (common_pos (m ∘ c)) (n := k)
  unfold prediction
  rw [Nat.mul_right_inj hc'.ne']
  calc
    _ ↔ (common m)^k * pattern M m = (common m)^k * pattern N m := (Nat.mul_right_inj hc.ne').symm
    _ ↔ _ := by rw [← scaled,← scaled,Nat.mul_right_inj (by positivity : (4:ℕ)^k ≠ 0)]

noncomputable def failures (f : Fin H → Label t b) (pairs : List (Fin t × Fin t)) : Finset (Fin H) := by
  classical exact univ.filter (fun i => ¬ ∀ p ∈ pairs, safe (f i) p)

theorem failure_bound (f : Fin H → Label t b) (L : ℕ) (hf : ∀ e, agreements f e ≤ L)
    (pairs : List (Fin t × Fin t)) : (failures f pairs).card ≤ L * pairs.length := by
  classical
  induction pairs with
  | nil => simp [failures]
  | cons p ps ih =>
    let bad := univ.filter (fun i => ¬safe (f i) p)
    have hsub : failures f (p::ps) ⊆ bad ∪ failures f ps := by
      intro i hi
      simp only [failures,mem_filter,mem_univ,true_and] at hi
      by_cases h : safe (f i) p
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,fun hz => hi (by simpa [h] using hz)⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hb' : bad.card ≤ L := by
      rcases lt_trichotomy p.1 p.2 with h|h|h
      · have hi : bad ⊆ univ.filter (fun i => f i p.1 = f i p.2) := by
          intro i hz; simp [bad,safe,h.ne] at hz; simpa using hz
        exact (card_le_card hi).trans (hf ⟨p,h⟩)
      · simp [bad,safe,h]
      · have hi : bad ⊆ univ.filter (fun i => f i p.2 = f i p.1) := by
          intro i hz; simp [bad,safe,h.ne.symm] at hz; simpa using hz.symm
        exact (card_le_card hi).trans (hf ⟨(p.2,p.1),h⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem protected_count (f : Fin H → Label t b) (L : ℕ) (hf : ∀ e, agreements f e ≤ L)
    (e : Pair t) (G : Model t k) :
    (failures f (critical e G)).card ≤ L*(5*k+1) :=
  (failure_bound f L hf _).trans (Nat.mul_le_mul_left L (critical_size e G))

theorem cost_scaled {I : Type} [Fintype I] (y : I → Option ℕ) (f : I → ℕ) (a : ℕ) (ha : 0 < a) :
    cost (fun i => (y i).map (a*·)) (fun i => a*f i) = cost y f := by
  unfold cost
  apply sum_congr rfl
  intro i _
  cases hi : y i with
  | none => simp [hi]
  | some n => simp [hi,Nat.mul_right_inj ha.ne']

theorem erasures_scaled {I : Type} [Fintype I] (y : I → Option ℕ) (a : ℕ) :
    erasures (fun i => (y i).map (a*·)) = erasures y := by simp [erasures]
end SpinHash

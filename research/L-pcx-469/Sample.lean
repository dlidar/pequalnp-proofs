import Mathlib
namespace SparseSampling
open Finset Real

def ind (b : Bool) : ℝ := if b then 1 else 0

theorem exp_quadratic (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1-x+x^2 := by
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
  have hp : 0 ≤ 1-x+x^2 := by nlinarith [sq_nonneg (x-1/2)]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hp
  nlinarith [mul_nonneg hx (sq_nonneg x)]

noncomputable def weight (x : ℝ) (b : Bool) : ℝ :=
  Real.exp ((4/9-x-ind b)*x + x^2/2)

theorem one_step {X : Type} [Fintype X] (b : X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b i)) :
    (∑ i, weight x (b i)) ≤ Fintype.card X := by
  let n : ℝ := Fintype.card X
  let a := (4/9-x)*x+x^2/2
  have exp_le_one : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
  have ht (z : Bool) : weight x z = Real.exp a * (1 - ind z * (1-Real.exp (-x))) := by
    cases z with
    | false => simp [weight,ind,a]
    | true =>
      change Real.exp ((4/9-x-1)*x+x^2/2) = Real.exp a * (1-1*(1-Real.exp (-x)))
      rw [one_mul,sub_sub_cancel,← Real.exp_add]
      congr 1; dsimp [a]; ring
  simp_rw [ht]
  rw [← mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one]
  change Real.exp a * (n - (∑ i, ind (b i)) * (1-Real.exp (-x))) ≤ n
  change 4*n ≤ _ at hd
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hα : n - (∑ i, ind (b i)) * (1-Real.exp (-x)) ≤ n*(1-a) := by
    have hq := exp_quadratic x hx
    have h₁ := mul_le_mul_of_nonneg_right (show 4/9*n ≤ ∑ i, ind (b i) by linarith) (sub_nonneg.mpr exp_le_one)
    have h₂ := mul_le_mul_of_nonneg_left (show x-x^2 ≤ 1-Real.exp (-x) by linarith) (show 0 ≤ 4/9*n by positivity)
    dsimp [a]
    nlinarith [mul_nonneg hn (sq_nonneg x)]
  have hneg := Real.add_one_le_exp (-a)
  calc
    _ ≤ Real.exp a * (n*(1-a)) := mul_le_mul_of_nonneg_left hα (Real.exp_pos _).le
    _ ≤ Real.exp a * (n*Real.exp (-a)) := by gcongr; linarith
    _ = n := by rw [← mul_left_comm,← Real.exp_add]; simp

theorem good_row {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i))
    (w : F → ℝ) (hw : ∀ f, 0 ≤ w f) :
    ∃ i, ∑ f, w f * weight x (b f i) ≤ ∑ f, w f := by
  classical
  by_contra! h
  have ha := Finset.sum_lt_sum_of_nonempty (s := (univ : Finset X)) univ_nonempty (fun i _ => h i)
  rw [show (∑ i, ∑ f, w f * weight x (b f i)) = ∑ f, ∑ i, w f * weight x (b f i) from Finset.sum_comm] at ha
  have hb : (∑ f, ∑ i, w f * weight x (b f i)) ≤ ∑ f, w f * Fintype.card X := by
    apply sum_le_sum
    intro f _
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (one_step _ _ hx (hd f)) (hw f)
  have hc : (∑ i : X, ∑ f, w f) = ∑ f, w f * Fintype.card X := by
    simp [← sum_mul, mul_comm]
  rw [← hc] at hb
  linarith

def hits {X F : Type} (b : F → X → Bool) (s : List X) (f : F) : ℝ :=
  (s.map (fun i => ind (b f i))).sum

noncomputable def score {X F : Type} (b : F → X → Bool) (s : List X) (f : F) (x : ℝ) :=
  Real.exp ((((4/9-x) * s.length - hits b s f)*x) + s.length*x^2/2)

theorem choose_batch {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i)) (d : ℕ) :
    ∃ s : List X, s.length = d ∧ ∑ f, score b s f x ≤ Fintype.card F := by
  induction d with
  | zero => exact ⟨[],rfl,by simp [score,hits]⟩
  | succ d ih =>
    obtain ⟨s,hs,hh⟩ := ih
    obtain ⟨i,hi⟩ := good_row b x hx hd (fun f => score b s f x) (fun _ => (Real.exp_pos _).le)
    refine ⟨i::s,by simp [hs], ?_⟩
    have he (f : F) : score b (i::s) f x = score b s f x * weight x (b f i) := by
      simp only [score,weight,hits,List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,← Real.exp_add]
      congr 1; ring
    simpa only [he] using hi.trans hh

theorem sparse_batch {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (s : ℕ) (hs : 0 < s)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i))
    (L : ℕ) (hL : Fintype.card F < 2^L) :
    ∃ batch : List X, batch.length = 2*s^2*L ∧
      ∀ f, (4/9-1/(s:ℝ))*batch.length ≤ hits b batch f := by
  let x : ℝ := 1/(s:ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  obtain ⟨B,hB,hcost⟩ := choose_batch b x hx.le hd (2*s^2*L)
  refine ⟨B,hB,fun f => ?_⟩
  have hscore : score b B f x ≤ Fintype.card F :=
    (Finset.single_le_sum (f := fun z => score b B z x) (fun z _ => (Real.exp_pos _).le) (Finset.mem_univ f)).trans hcost
  have hbound : (Fintype.card F : ℝ) < Real.exp (L:ℝ) := by
    have hh : (Fintype.card F : ℝ) < (2:ℝ)^L := by exact_mod_cast hL
    refine hh.trans_le ?_
    simpa [← Real.exp_nat_mul] using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) Real.exp_one_gt_two.le L)
  have hnorm : (B.length:ℝ)*x^2/2 = L := by
    rw [hB]; dsimp [x]; push_cast; field_simp <;> ring
  unfold score at hscore
  rw [hnorm] at hscore
  have hn := Real.exp_lt_exp.mp (hscore.trans_lt hbound)
  change (4/9-x)*B.length ≤ _
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr h) hx]
end SparseSampling

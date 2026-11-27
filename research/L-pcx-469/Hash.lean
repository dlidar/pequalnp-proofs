import Short
namespace SpinHash
open Finset SpinMass
abbrev Label (t b : ℕ) := Fin t → Fin b

def colorFill {t b : ℕ} (e : Pair t) (r : Away e → Fin b) (x y : Fin b) (i : Fin t) : Fin b :=
  if h : i = e.val.1 then x else if h' : i = e.val.2 then y else r ⟨i,h,h'⟩
def colorEquiv {t b : ℕ} (e : Pair t) : Label t b ≃ (Away e → Fin b) × (Fin b × Fin b) where
  toFun p := (fun i => p i.val, p e.val.1, p e.val.2)
  invFun a := colorFill e a.1 a.2.1 a.2.2
  left_inv p := by
    funext i; simp only [colorFill]
    split <;> first | simp_all | split <;> simp_all
  right_inv a := by
    rcases a with ⟨r,x,y⟩
    simp [colorFill,(ne_of_lt e.property).symm]
    funext i; simp [i.property.1,i.property.2]

def multiplier {t b : ℕ} (e : Pair t) (c : Label t b) : ℝ :=
  if c e.val.1 = c e.val.2 then 2 else 1

theorem moment {t b : ℕ} (e : Pair t) (hb : 0 < b) :
    (∑ c : Label t b, multiplier e c) = (Fintype.card (Label t b) : ℝ)*(1+1/b) := by
  have ht := Fintype.card_congr (colorEquiv (b := b) e)
  let N := Fintype.card (Away e → Fin b)
  change Fintype.card (Label t b) = _ at ht
  simp only [Fintype.card_prod,Fintype.card_fin] at ht
  change Fintype.card (Label t b) = N*(b*b) at ht
  rw [ht,← (colorEquiv (b := b) e).symm.sum_comp (multiplier e),Fintype.sum_prod_type]
  have block (r : Away e → Fin b) : (∑ z : Fin b × Fin b, multiplier e ((colorEquiv e).symm (r,z))) = (b:ℝ)*(b+1) := by
    rw [Fintype.sum_prod_type]
    have hv (x y : Fin b) : multiplier e ((colorEquiv e).symm (r,x,y)) = (1:ℝ) + if x = y then 1 else 0 := by
      change (if colorFill e r x y e.val.1 = colorFill e r x y e.val.2 then (2:ℝ) else 1) = _
      by_cases h : x = y <;> simp [colorFill,(ne_of_lt e.property).symm,h] <;> norm_num
    simp_rw [hv, sum_add_distrib]
    simp; ring
  simp_rw [block]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_mul]
  change (N:ℝ)*(_*_) = _; field_simp <;> ring

def agreements {t b H : ℕ} (f : Fin H → Label t b) (e : Pair t) :=
  (univ.filter (fun i => f i e.val.1 = f i e.val.2)).card

theorem prod_multiplier {t b H : ℕ} (f : Fin H → Label t b) (e : Pair t) :
    (∏ i, multiplier e (f i)) = 2^agreements f e := by
  have hi (i : Fin H) : multiplier e (f i) = (2:ℝ)^(if f i e.val.1 = f i e.val.2 then 1 else 0 : ℕ) := by
    unfold multiplier; split <;> simp_all
  simp_rw [hi]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact sum_boole _ _

theorem multiplicative_bound {b : ℕ} (hb : 0 < b) : (1+1/(b:ℝ))^b ≤ 4 := by
  have h := Real.add_one_le_exp (1/(b:ℝ))
  rw [add_comm] at h
  refine (pow_le_pow_left₀ (by positivity) h b).trans ?_
  rw [← Real.exp_nat_mul]
  have hn : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [show (b:ℝ)*(1/b) = 1 by field_simp]
  linarith [Real.exp_one_lt_three]

theorem hash_family (t b L : ℕ) (hb : 0 < b) (hs : Fintype.card (Pair t) < 2^L) :
    ∃ f : Fin (b*L) → Label t b, ∀ e, agreements f e < 3*L := by
  classical
  let H := b*L
  let X := Label t b
  let n : ℝ := Fintype.card X
  haveI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hm (e : Pair t) :
      (∑ f : Fin H → X, (2:ℝ)^agreements f e) = n^H * (1+1/(b:ℝ))^H := by
    simp_rw [← prod_multiplier]
    rw [← Fintype.prod_sum (fun (_ : Fin H) (c : X) => multiplier e c)]
    simp only [prod_const,card_univ,Fintype.card_fin]
    rw [moment e hb,mul_pow]
  have hbnd : (1+1/(b:ℝ))^H ≤ 4^L := by
    dsimp [H]; rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (multiplicative_bound hb) _
  have hsum : (∑ f : Fin H → X, ∑ e : Pair t, (2:ℝ)^agreements f e) < n^H*2^(3*L) := by
    rw [Finset.sum_comm]
    simp_rw [hm]
    simp only [sum_const,card_univ,nsmul_eq_mul]
    have h' : (Fintype.card (Pair t) : ℝ) < (2:ℝ)^L := by exact_mod_cast hs
    calc
      _ = n^H * ((Fintype.card (Pair t) : ℝ) * (1+1/(b:ℝ))^H) := by ring
      _ ≤ n^H * ((Fintype.card (Pair t) : ℝ) * 4^L) := by gcongr
      _ < n^H * ((2:ℝ)^L * 4^L) := by gcongr
      _ = _ := by rw [← mul_pow,show 3*L = 3 * L by rfl, pow_mul (2:ℝ) 3 L]; norm_num
  by_contra! h
  have hlo (f : Fin H → X) : (2:ℝ)^(3*L) ≤ ∑ e : Pair t, (2:ℝ)^agreements f e := by
    obtain ⟨e,he⟩ := h f
    exact (pow_le_pow_right₀ (by norm_num) he).trans
      (Finset.single_le_sum (f := fun z => (2:ℝ)^agreements f z) (fun _ _ => by positivity) (mem_univ e))
  have hh := Finset.sum_le_sum (s := univ) (fun f _ => hlo f)
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow] at hh
  exact (not_lt_of_ge hh) hsum

end SpinHash

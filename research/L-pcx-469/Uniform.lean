import Code
namespace SpinMass
open Finset
variable {t k : ℕ}

abbrev Away (e : Pair t) := {i : Fin t // i ≠ e.val.1 ∧ i ≠ e.val.2}
def fill (e : Pair t) (r : Away e → Fin 3) (x y : Fin 3) (i : Fin t) : Fin 3 :=
  if h : i = e.val.1 then x else if h' : i = e.val.2 then y else r ⟨i,h,h'⟩

def maskEquiv (e : Pair t) : Mask t ≃ (Away e → Fin 3) × (Fin 3 × Fin 3) where
  toFun p := (fun i => p i.val, p e.val.1, p e.val.2)
  invFun a := fill e a.1 a.2.1 a.2.2
  left_inv p := by
    funext i
    simp only [fill]
    split <;> first | simp_all | split <;> simp_all
  right_inv a := by
    rcases a with ⟨r,x,y⟩
    have hi := ne_of_lt e.property
    simp [fill,hi.symm]
    funext i
    simp [i.property.1,i.property.2]

theorem vary_fill (e : Pair t) (r : Away e → Fin 3) (x y : Fin 3) :
    vary e (fill e r 0 0) x y = fill e r x y := by
  funext i; unfold vary fill; split_ifs <;> rfl

theorem dimensions (e : Pair t) : 3^t = 9 * Fintype.card (Away e → Fin 3) := by
  have h := Fintype.card_congr (maskEquiv e)
  change Fintype.card (Fin t → Fin 3) = _ at h
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,show 3*3=9 by decide,Nat.mul_comm 9] using h

theorem support_sum (e : Pair t) (f : Mask t → ℕ) :
    (∑ p, f p) = ∑ r : Away e → Fin 3, ∑ x : Fin 3, ∑ y : Fin 3, f (fill e r x y) := by
  rw [← (maskEquiv e).symm.sum_comp f, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type]
  rfl

def dist {ι : Type} [Fintype ι] (u v : ι → ℕ) : ℕ :=
  ∑ i, if u i ≠ v i then 1 else 0

theorem full_distance (G H : Fin k → Option (Pair t)) (e : Pair t) (h : mult G e ≠ mult H e) :
    4 * 3^t ≤ 9 * dist (reading G) (reading H) := by
  have hf (r : Away e → Fin 3) := four_masks G H e (fill e r 0 0) h
  simp_rw [vary_fill] at hf
  have hd := Finset.sum_le_sum (s := (univ : Finset (Away e → Fin 3))) (fun r _ => hf r)
  rw [← support_sum e (fun p => if reading G p ≠ reading H p then 1 else 0)] at hd
  simp only [sum_const,card_univ,nsmul_eq_mul] at hd
  change Fintype.card (Away e → Fin 3) * 4 ≤ _ at hd
  rw [dimensions e]
  unfold dist
  omega

def erasures {ι : Type} [Fintype ι] (y : ι → Option ℕ) : ℕ :=
  ∑ i, if y i = none then 1 else 0
def cost {ι : Type} [Fintype ι] (y : ι → Option ℕ) (u : ι → ℕ) : ℕ :=
  ∑ i, if y i ≠ none ∧ y i ≠ some (u i) then 1 else 0

theorem cost_triangle {ι : Type} [Fintype ι] (y : ι → Option ℕ) (u v : ι → ℕ) :
    dist u v ≤ cost y u + cost y v + erasures y := by
  unfold dist cost erasures
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  by_cases h : u i = v i <;> by_cases hh : y i = none <;> by_cases ha : y i = some (u i) <;>
    by_cases hb : y i = some (v i) <;> simp_all

theorem nearest_recovers (G H : Fin k → Option (Pair t)) (y : Mask t → Option ℕ)
    (hc : cost y (reading H) ≤ cost y (reading G))
    (hr : 9 * (2 * cost y (reading G) + erasures y) < 4 * 3^t) :
    ∀ e, mult H e = mult G e := by
  intro e
  by_contra hn
  have hl := full_distance H G e hn
  have hu := cost_triangle y (reading H) (reading G)
  omega

end SpinMass

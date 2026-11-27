import Uniform
import Sample
namespace SpinMass
open Finset SparseSampling
variable {t k : ℕ}
abbrev Model (t k : ℕ) := Fin k → Option (Pair t)
def slotBits (t k : ℕ) := 4 * k * (1 + Nat.log 2 t) + 1
theorem count_models (t k : ℕ) :
    Fintype.card (Model t k × Model t k) < 2^slotBits t k := by
  let b := 1 + Nat.log 2 t
  have ht : t+1 ≤ 2^b := by simpa [b,Nat.add_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
  have hp : Fintype.card (Pair t) ≤ t*t := by
    simpa using Fintype.card_le_of_injective (fun e : Pair t => e.val) Subtype.val_injective
  have ho : Fintype.card (Option (Pair t)) ≤ (2^b)^2 := by
    rw [Fintype.card_option]
    calc
      _ ≤ (t+1)^2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_left ht 2
  have hM : Fintype.card (Model t k) ≤ 2^(b*2*k) := by
    simpa [Model, Fintype.card_fun, pow_mul] using Nat.pow_le_pow_left ho k
  rw [Fintype.card_prod]
  refine (Nat.mul_le_mul hM hM).trans_lt ?_
  rw [← pow_add]
  change 2^_ < 2^(4*k*b+1)
  apply Nat.pow_lt_pow_right (by decide)
  ring_nf; omega

def distinguish (z : Model t k × Model t k) (p : Mask t) : Bool :=
  decide ((∀ e, mult z.1 e = mult z.2 e) ∨ reading z.1 p ≠ reading z.2 p)

theorem ind_case (P : Prop) [Decidable P] : ind (decide P) = ((if P then 1 else 0 : ℕ) : ℝ) := by
  by_cases h : P <;> simp [h,ind]

theorem dist_at (G H : Model t k) (hn : ¬∀ e, mult G e = mult H e) (p : Mask t) :
    ind (distinguish (G,H) p) = ((if reading G p ≠ reading H p then 1 else 0 : ℕ) : ℝ) := by
  unfold distinguish
  simp only [hn,false_or]
  exact ind_case _

theorem distinguish_density (z : Model t k × Model t k) :
    4 * (Fintype.card (Mask t) : ℝ) ≤ 9 * ∑ p, ind (distinguish z p) := by
  by_cases h : ∀ e, mult z.1 e = mult z.2 e
  · have hh (p : Mask t) : ind (distinguish z p) = 1 := by
      have hc : (∀ e, mult z.1 e = mult z.2 e) ∨ reading z.1 p ≠ reading z.2 p := Or.inl h
      unfold distinguish; rw [decide_eq_true hc]; rfl
    simp only [hh,sum_const,card_univ,nsmul_eq_mul,mul_one]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Mask t))]
  · obtain ⟨e,he⟩ := Classical.not_forall.mp h
    have hd := full_distance z.1 z.2 e he
    have hv (p : Mask t) : ind (distinguish z p) = ((if reading z.1 p ≠ reading z.2 p then 1 else 0 : ℕ) : ℝ) := by
      exact dist_at z.1 z.2 h p
    simp_rw [hv,← Nat.cast_sum]
    change 4 * (Fintype.card (Fin t → Fin 3) : ℝ) ≤ _
    simp only [Fintype.card_fun,Fintype.card_fin]
    exact_mod_cast hd

theorem hits_get {X F : Type} (b : F → X → Bool) (l : List X) (f : F) :
    hits b l f = ∑ i : Fin l.length, ind (b f (l.get i)) := by
  rw [← List.sum_ofFn]
  unfold hits
  congr 1
  apply List.ext_getElem
  · simp
  · intros; simp

def rowDist {d : ℕ} (batch : Fin d → Mask t) (G H : Model t k) :=
  dist (fun i => reading G (batch i)) (fun i => reading H (batch i))

theorem short_distance (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ d : ℕ, ∃ batch : Fin d → Mask t, d = 2*s^2*slotBits t k ∧
      ∀ (G H : Model t k) (e : Pair t), mult G e ≠ mult H e →
      (4*s-9)*d ≤ 9*s*rowDist batch G H := by
  obtain ⟨B,hB,hfit⟩ := sparse_batch distinguish s (by omega) distinguish_density (slotBits t k) (count_models t k)
  refine ⟨B.length,B.get,hB,fun G H e he => ?_⟩
  have hh := hfit (G,H)
  rw [hits_get] at hh
  have hn : ¬ ∀ e, mult G e = mult H e := fun z => he (z e)
  have hu (i : Fin B.length) : ind (distinguish (G,H) (B.get i)) =
      ((if reading G (B.get i) ≠ reading H (B.get i) then 1 else 0 : ℕ) : ℝ) := by
    exact dist_at G H hn (B.get i)
  simp_rw [hu,← Nat.cast_sum] at hh
  change _ ≤ (rowDist B.get G H : ℝ) at hh
  have hs' : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  field_simp at hh
  have h₉ : 9 ≤ 4*s := by omega
  exact_mod_cast (show (((4*s-9:ℕ):ℝ)*B.length) ≤ 9*(s:ℝ)*rowDist B.get G H by
    rw [Nat.cast_sub h₉]; push_cast; nlinarith)

theorem short_recovers (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ d : ℕ, ∃ batch : Fin d → Mask t, d = 2*s^2*slotBits t k ∧
    ∀ (G H : Model t k) (y : Fin d → Option ℕ),
      let word := fun (M : Model t k) i => reading M (batch i)
      9*s*(2*cost y (word G)+erasures y) < (4*s-9)*d →
      cost y (word H) ≤ cost y (word G) → ∀ e, mult H e = mult G e := by
  obtain ⟨d,batch,hd,hh⟩ := short_distance t k s hs
  refine ⟨d,batch,hd,fun G H y hr hc e => ?_⟩
  by_contra hn
  have hlo := hh H G e hn
  have htr := cost_triangle y (fun i => reading H (batch i)) (fun i => reading G (batch i))
  dsimp only at hr hc
  have hle := Nat.mul_le_mul_left (9*s) (show rowDist batch H G ≤ 2*cost y (fun i => reading G (batch i))+erasures y by unfold rowDist; omega)
  omega

end SpinMass

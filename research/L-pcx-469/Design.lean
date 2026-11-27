import Combine
namespace SpinHash
open Finset SpinMass

def colors (k s : ℕ) := 128*((k+1)*s)
def outerL (t : ℕ) := 2*(1+Nat.log 2 t)
def outer (t k s : ℕ) := colors k s * outerL t
def inner (k s : ℕ) := 2*(2*s)^2 * slotBits (colors k s) k

theorem log_colors (k s : ℕ) (hs : 0 < s) : Nat.log 2 (colors k s) ≤ 7+Nat.log 2 ((k+1)*s) := by
  let x := (k+1)*s
  have hx : 0 < x := Nat.mul_pos (by omega) hs
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  have hh := Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2^7)
  rw [← pow_add] at hh
  have hlt := Nat.log_lt_of_lt_pow (b := 2) (by dsimp [colors]; positivity : colors k s ≠ 0)
    (show colors k s < 2^(7+(Nat.log 2 x).succ) from hh)
  change Nat.log 2 (colors k s) ≤ 7+Nat.log 2 x;omega

theorem query_budget (t k s : ℕ) (hs : 0 < s) :
    outer t k s * inner k s ≤ 67584*(k+1)^2*s^3*(1+Nat.log 2 ((k+1)*s))*(1+Nat.log 2 t) := by
  have hl := log_colors k s hs
  let u := Nat.log 2 ((k+1)*s)
  have ha : slotBits (colors k s) k ≤ 33*(k+1)*(1+u) := by
    unfold slotBits
    change Nat.log 2 (colors k s) ≤ 7+u at hl
    have h := Nat.mul_le_mul_left (4*k) (Nat.add_le_add_left hl 1)
    nlinarith
  have hb := Nat.mul_le_mul_left (outer t k s*(2*(2*s)^2)) ha
  change outer t k s * (2*(2*s)^2*slotBits (colors k s) k) ≤ _
  unfold outer colors outerL at *
  dsimp [u] at *
  nlinarith

theorem local_design (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ (f : Fin (outer t k s) → Label t (colors k s))
      (m : Fin (inner k s) → Mask (colors k s)),
      ∀ (G : Model t k) (e : Pair t) (y : Fin (outer t k s) → Fin (inner k s) → Option ℕ),
      9*s*(2*totalErrors f m G y + totalLost y) < (4*s-9)*(outer t k s * inner k s) →
      ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) y < totalPrice k f m e a y := by
  let b := colors k s
  let L := outerL t
  have hb : 0 < b := by dsimp [b,colors]; positivity
  have hnum : Fintype.card (Pair t) < 2^L := by
    have hp : Fintype.card (Pair t) ≤ t*t := by
      simpa using Fintype.card_le_of_injective (fun e : Pair t => e.val) Subtype.val_injective
    have ht := Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
    have hsq : t*t < 2^(Nat.log 2 t).succ * 2^(Nat.log 2 t).succ := by nlinarith [Nat.mul_le_mul (show t+1 ≤ 2^(Nat.log 2 t).succ from ht) (show t+1 ≤ 2^(Nat.log 2 t).succ from ht)]
    dsimp [L,outerL];rw [two_mul, pow_add]
    simpa [Nat.add_comm 1] using hp.trans_lt hsq
  obtain ⟨f,hf⟩ := hash_family t b L hb hnum
  obtain ⟨d,m,hd,hm⟩ := short_distance b k (2*s) (by omega)
  subst d
  refine ⟨f,m,fun G e y hr => ?_⟩
  apply aggregate s hs f m G e y _ _ hr
  · intro M N q hn
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm M N q hn
  · have hh := protected_count f (3*L) (fun e => (hf e).le) e G
    have h := Nat.mul_le_mul_left (4*s) hh
    change 4*s*(failures f (critical e G)).card ≤ b*L
    apply h.trans
    dsimp [b,colors]; nlinarith

end SpinHash

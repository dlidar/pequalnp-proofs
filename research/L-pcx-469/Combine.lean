import LocalFit
namespace SpinHash
open Finset SpinMass
variable {t b k H I : ℕ}

def totalErrors (f : Fin H → Label t b) (m : Fin I → Mask b)
    (G : Model t k) (y : Fin H → Fin I → Option ℕ) :=
  ∑ i, cost (y i) (blockWord (f i) m G)
def totalLost (y : Fin H → Fin I → Option ℕ) := ∑ i, erasures (y i)
noncomputable def totalPrice (k : ℕ) (f : Fin H → Label t b) (m : Fin I → Mask b)
    (e : Pair t) (a : ℕ) (y : Fin H → Fin I → Option ℕ) :=
  ∑ i, price k (f i) m e a (y i)

theorem aggregate (s : ℕ) (hs : 3 ≤ s) (f : Fin H → Label t b) (m : Fin I → Mask b)
    (G : Model t k) (e : Pair t) (y : Fin H → Fin I → Option ℕ)
    (hsep : ∀ (M N : Model b k) (q : Pair b), mult M q ≠ mult N q → (8*s-9)*I ≤ 18*s*rowDist m M N)
    (hf : 4*s*(failures f (critical e G)).card ≤ H)
    (hr : 9*s*(2*totalErrors f m G y+totalLost y) < (4*s-9)*(H*I)) :
    ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) y < totalPrice k f m e a y := by
  classical
  intro a ha
  let bad := failures f (critical e G)
  let z := fun i : Fin H => if i ∈ bad then 1 else 0
  have hz : ∑ i, z i = bad.card := by simp [z]
  have good (i : Fin H) (hi : i ∉ bad) : ∀ p ∈ critical e G, safe (f i) p := by
    simpa [bad,failures] using hi
  let E := totalErrors f m G y
  let D := totalLost y
  let T := totalPrice k f m e (mult G e) y
  let F := totalPrice k f m e a y
  have htrue (i : Fin H) : price k (f i) m e (mult G e) (y i) ≤ cost (y i) (blockWord (f i) m G) + I*z i := by
    by_cases hi : i ∈ bad
    · simp [z,hi]; have hh := price_cap k (f i) m e (mult G e) (y i); omega
    · simpa [z,hi] using price_true (good i hi) m (y i)
  have ht := sum_le_sum (s := univ) (fun i _ => htrue i)
  rw [sum_add_distrib,← mul_sum,hz] at ht
  change T ≤ E + I * bad.card at ht
  let A := (8*s-9)*I
  have hfalse (i : Fin H) : A ≤ 18*s*(price k (f i) m e a (y i) +
      cost (y i) (blockWord (f i) m G) + erasures (y i)) + A*z i := by
    by_cases hi : i ∈ bad
    · simp [z,hi]
    · simpa [A,z,hi] using price_false (good i hi) s a ha m (y i) hsep
  have ht' := sum_le_sum (s := univ) (fun i _ => hfalse i)
  simp only [sum_add_distrib,← mul_sum,hz,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at ht'
  change H*A ≤ 18*s*(F+E+D)+A*bad.card at ht'
  change 4*s*bad.card ≤ H at hf
  change 9*s*(2*E+D) < (4*s-9)*(H*I) at hr
  change T < F
  by_contra! hn
  have hupper := Nat.mul_le_mul_left (18*s) (show F+E+D ≤ 2*E+D+I*bad.card by omega)
  have hbad := Nat.mul_le_mul_right (9*I) hf
  have hgap := Nat.mul_lt_mul_of_pos_left hr (by decide : 0 < 2)
  have hx : 8*s-9+9=8*s := by omega
  have hy : 4*s-9+9=4*s := by omega
  have hA := congrArg (fun n : ℕ => n * (H*I)) hx
  have hB := congrArg (fun n : ℕ => n * (H*I)) hy
  have hsmall := Nat.mul_le_mul_right (I*bad.card) (show 8*s-9 ≤ 8*s by omega)
  dsimp only [A] at ht'
  nlinarith

end SpinHash

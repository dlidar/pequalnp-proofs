import Density
import PEqualNP.Outside.L_meta_5351

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.Research.ReadTwoDensity

namespace PEqualNP.Research.PlaneResidual

theorem boundedOrders (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (hsmall : q ≤ 349) : N*q ≤ 100*C.size := by
  have lower := PEqualNP.Outside.L_meta_5351 q N S C hq hN hc hu h hr hf
  simpa only [Nat.mul_comm 349 N] using (Nat.mul_le_mul_left N hsmall).trans (by simpa only [Nat.mul_comm 349 N] using lower)

theorem residual (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output < N+N+C.size) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (short : 100*C.size < N*q) :
    350 ≤ q ∧ 467*(N*(q+1)) < 1000*(hardFlags S C).card := by
  have large : 350 ≤ q := by
    by_contra! small
    have := boundedOrders q N S C hq hN hc hu h hr hf (by omega)
    omega
  refine ⟨large,?_⟩
  have t := hardFlagTradeoff q N S C hq hN hc hu h ho hr hf
  have hqN : 350*N ≤ N*q := by nlinarith [Nat.mul_le_mul_left N large]
  have hlarge : 40000 ≤ N := by nlinarith [Nat.mul_self_le_mul_self hq]
  simp only [Nat.mul_add,Nat.mul_one] at t ⊢
  omega

end PEqualNP.Research.PlaneResidual

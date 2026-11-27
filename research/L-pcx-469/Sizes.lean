import Design
namespace SpinHash
open SpinMass
def scale (t k s : ℕ) := (t+2)*(k+s+2)^(k+1)
def cap (t k s : ℕ) := (scale t k s)^32

theorem parameter_bounds (t k s : ℕ) (ht : 2 ≤ t) (hk : 0 < k) (hs : 3 ≤ s) :
    let U := cap t k s
    4  ≤  U ∧ k*(2*t+2)+1  ≤  U ∧ inner k s  ≤  U ∧ outer t k s * inner k s+1  ≤  U ∧
    Fintype.card (Model (colors k s) k)  ≤  U ∧ k+1  ≤  U ∧
    Fintype.card (Pair t × Fin (k+1))  ≤  U := by
  dsimp only
  let v := k+s+2
  let P := scale t k s
  have hv : 6 ≤ v := by dsimp [v];omega
  have hv1 : 1 ≤ v := by omega
  have hvk : v  ≤  v^(k+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hv1 (show 1 ≤ k+1 by omega)
  have hvs : v^(k+1)  ≤  P := by dsimp [P,scale];change v^_  ≤  (t+2)*v^_;nlinarith
  have hvt : t+2 ≤ P := by dsimp [P,scale];change t+2 ≤ (t+2)*v^_;nlinarith
  have hP := hvk.trans hvs
  have h4 : 6 ≤ P := hv.trans hP
  have hpow (a c : ℕ) (hac : a ≤ c) : P^a  ≤  P^c := Nat.pow_le_pow_right (by omega) hac
  have hp32 : P  ≤  P^32 := by simpa only [pow_one] using hpow 1 32 (by decide)
  have hu : k+1  ≤  P := by dsimp [v] at hP;omega
  have hss : s  ≤  P := by dsimp [v] at hP;omega
  have hprod : (k+1)*s  ≤  P^2 := by simpa [pow_two] using Nat.mul_le_mul hu hss
  have hlog : 1+Nat.log 2 ((k+1)*s)  ≤  P^3 := by
    have hh := (Nat.log_le_self 2 _).trans hprod
    nlinarith [Nat.mul_le_mul_left (P^2) h4]
  have hlogt : 1+Nat.log 2 t  ≤  P := by have := Nat.log_le_self 2 t;omega
  have hnum : 67584  ≤  P^7 := by
    exact (by decide : 67584  ≤  6^7).trans (Nat.pow_le_pow_left h4 7)
  have hd := (query_budget t k s (by omega)).trans
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hnum (Nat.pow_le_pow_left hu 2)) (Nat.pow_le_pow_left hss 3)) hlog) hlogt)
  have hds : outer t k s * inner k s  ≤  P^16 := hd.trans_eq (by ring)
  have hd' : outer t k s * inner k s + 1  ≤  P^32 := by
    have hx : P^16 < P^32 := Nat.pow_lt_pow_right (by omega) (by decide)
    omega
  have hout : 0 < outer t k s := by unfold outer colors outerL;positivity
  have hin : inner k s  ≤  outer t k s * inner k s := Nat.le_mul_of_pos_left _ hout
  have hW : k*(2*t+2)+1  ≤  P^3 := by
    have hx := Nat.mul_le_mul (show k ≤ P by omega) (show 2*t+2 ≤ 2*P by omega)
    nlinarith [Nat.mul_le_mul_left (P^2) h4]
  have hvCube : 128  ≤  v^3 := (by decide : 128 ≤ 6^3).trans (Nat.pow_le_pow_left hv 3)
  have hb : colors k s  ≤  v^5 := by
    have hk' : k+1 ≤ v := by dsimp [v];omega
    have hs' : s ≤ v := by dsimp [v];omega
    exact (Nat.mul_le_mul hvCube (Nat.mul_le_mul hk' hs')).trans_eq (by ring)
  have hcard (z : ℕ) : Fintype.card (Pair z)  ≤  z*z := by
    simpa using Fintype.card_le_of_injective (fun e : Pair z => e.val) Subtype.val_injective
  have hopt : Fintype.card (Option (Pair (colors k s)))  ≤  v^11 := by
    rw [Fintype.card_option]
    have h := (hcard _).trans (Nat.mul_le_mul hb hb)
    nlinarith [Nat.mul_le_mul_left (v^10) hv, Nat.one_le_pow 10 v (by omega)]
  have hmodel : Fintype.card (Model (colors k s) k)  ≤  P^11 := by
    change Fintype.card (Fin k → Option (Pair (colors k s)))  ≤  P^11
    simp only [Fintype.card_fun,Fintype.card_fin]
    calc
      _  ≤  (v^11)^k := Nat.pow_le_pow_left hopt k
      _  ≤  (v^(k+1))^11 := by rw [← pow_mul,← pow_mul];apply Nat.pow_le_pow_right hv1;omega
      _  ≤  _ := Nat.pow_le_pow_left hvs 11
  have hj : Fintype.card (Pair t × Fin (k+1))  ≤  P^3 := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact (Nat.mul_le_mul ((hcard t).trans (Nat.mul_le_mul (by omega : t ≤ P) (by omega : t ≤ P))) hu).trans_eq (by ring)
  exact ⟨by change 4 ≤ P^32;omega,hW.trans (hpow 3 32 (by decide)),by change _  ≤  P^32;omega,hd',
    hmodel.trans (hpow 11 32 (by decide)),hu.trans hp32,hj.trans (hpow 3 32 (by decide))⟩

theorem final_size (t k s : ℕ) : (cap t k s)^37 = (t+2)^1184*(k+s+2)^(1184*(k+1)) := by
  unfold cap scale
  rw [← pow_mul,mul_pow,← pow_mul,show 32*37=1184 by decide,Nat.mul_comm (k+1)]
end SpinHash

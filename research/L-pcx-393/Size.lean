import InventoryBound
namespace PinStates
theorem sqrt_double (n : ℕ) : Nat.sqrt (2*n)+1 ≤ 2*(Nat.sqrt n+1) := by
  have a := Nat.lt_succ_sqrt n
  have b : 2*n < (2*(Nat.sqrt n+1))^2 := by nlinarith
  have := Nat.sqrt_lt'.mpr b
  omega
theorem small_poly (n : ℕ) : 2*n+2 ≤ 2^(4*(Nat.sqrt n+1)) := by
  let r := Nat.sqrt n+1
  have a : n < r^2 := by have := Nat.lt_succ_sqrt n; dsimp [r]; nlinarith
  have b : r ≤ 2^r := Nat.le_of_lt (Nat.lt_two_pow_self)
  have c : r^2 ≤ (2^r)^2 := Nat.pow_le_pow_left b 2
  calc 2*n+2 ≤ 2*(r^2) := by omega
       _ ≤ 2*((2^r)^2) := by omega
       _ = 2^(r*2+1) := by rw [pow_succ 2 (r*2),pow_mul]; ring
       _ ≤ 2^(4*(Nat.sqrt n+1)) := Nat.pow_le_pow_right (by decide) (by dsimp [r];omega)
theorem live_states {n : ℕ} (hn : 0<n) : (states (2*n)).card ≤ 2^(160*(Nat.sqrt n+1)) := by
  have h := state_count (m:=2*n) (by omega)
  have p : 2*n+1 ≤ 2^(4*(Nat.sqrt n+1)) := (Nat.le_succ _).trans (small_poly n)
  have q : (9:ℕ) ≤ 2^(4*(Nat.sqrt n+1)) := (show 9 ≤ 2^4 by decide).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have sq := sqrt_double n
  calc _ ≤ _ := h
       _ ≤ ((2^(4*(Nat.sqrt n+1)))*(2^(4*(Nat.sqrt n+1)))^4)*2^(140*(Nat.sqrt n+1)) := by
           exact Nat.mul_le_mul (Nat.mul_le_mul q (Nat.pow_le_pow_left p 4))
             (Nat.pow_le_pow_right (by decide) (by omega))
       _ = _ := by rw [← pow_mul,← pow_add,← pow_add]; congr 1; omega
end PinStates

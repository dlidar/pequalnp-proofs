import PEqualNP.Research.L_meta_2341_data

namespace PEqualNP.Research.PuncturedFlags
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

def packedByte : ℕ := 95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224
def byte (x : ℕ) := (packedByte >>> (4*(x%256)))%16
def countBytes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, x => byte x + countBytes n (x >>> 8)

theorem byte_ok (x : ℕ) : byte x = (List.range 8).countP x.testBit := by
  have tab : ∀ k : Fin 256, byte k.val = (List.range 8).countP k.val.testBit := by decide +kernel
  have e : byte x = byte (x%256) := by simp [byte]
  rw [e,tab ⟨x%256,Nat.mod_lt _ (by decide)⟩]
  apply List.countP_congr
  intro i hi
  have h : i < 8 := List.mem_range.mp hi
  change ((x%2^8).testBit i = true ↔ _)
  rw [Nat.testBit_mod_two_pow]
  simp [h]
theorem count_ok (n x : ℕ) : countBytes n x = (List.range (8*n)).countP x.testBit := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [show 8*(n+1) = 8+(8*n) by omega,List.range_add,List.countP_append,List.countP_map,countBytes,byte_ok,ih]
    congr 1
    apply List.countP_congr
    intro i _; simp [Function.comp_def,Nat.testBit_shiftRight]

/-- Count 256 bits with bounded reduction depth. -/
def pop : ℕ → ℕ → ℕ
  | 0,x => byte x
  | t+1,x => pop t x + pop t (x >>> (8 * 2^t))

theorem pop_correct (t x : ℕ) : pop t x = (List.range (8*2^t)).countP x.testBit := by
  induction t generalizing x with
  | zero => simpa [pop] using byte_ok x
  | succ t ih =>
    rw [show 8*2^(t+1) = 8*2^t + 8*2^t by rw [pow_succ]; omega,List.range_add,
      List.countP_append,List.countP_map,pop,ih,ih]
    congr 1
    apply List.countP_congr
    intro i _; simp [Nat.testBit_shiftRight,Function.comp_def]

def loss1 (a : Fin 26) := pop 5 (column a)
def loss2 (a b : Fin 26) := pop 5 (column a &&& column b)
def loss3 (a b c : Fin 26) := pop 5 (column a &&& column b &&& column c)

theorem one_lower : ∀ a : Fin 26, 135 ≤ loss1 a := by decide +kernel
theorem two_lower : ∀ a b : Fin 26, 81 ≤ loss2 a b := by decide +kernel
private theorem lower0 : ∀ b c : Fin 26, (0 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 0 b c := by decide +kernel
private theorem lower1 : ∀ b c : Fin 26, (1 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 1 b c := by decide +kernel
private theorem lower2 : ∀ b c : Fin 26, (2 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 2 b c := by decide +kernel
private theorem lower3 : ∀ b c : Fin 26, (3 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 3 b c := by decide +kernel
private theorem lower4 : ∀ b c : Fin 26, (4 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 4 b c := by decide +kernel
private theorem lower5 : ∀ b c : Fin 26, (5 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 5 b c := by decide +kernel
private theorem lower6 : ∀ b c : Fin 26, (6 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 6 b c := by decide +kernel
private theorem lower7 : ∀ b c : Fin 26, (7 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 7 b c := by decide +kernel
private theorem lower8 : ∀ b c : Fin 26, (8 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 8 b c := by decide +kernel
private theorem lower9 : ∀ b c : Fin 26, (9 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 9 b c := by decide +kernel
private theorem lower10 : ∀ b c : Fin 26, (10 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 10 b c := by decide +kernel
private theorem lower11 : ∀ b c : Fin 26, (11 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 11 b c := by decide +kernel
private theorem lower12 : ∀ b c : Fin 26, (12 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 12 b c := by decide +kernel
private theorem lower13 : ∀ b c : Fin 26, (13 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 13 b c := by decide +kernel
private theorem lower14 : ∀ b c : Fin 26, (14 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 14 b c := by decide +kernel
private theorem lower15 : ∀ b c : Fin 26, (15 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 15 b c := by decide +kernel
private theorem lower16 : ∀ b c : Fin 26, (16 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 16 b c := by decide +kernel
private theorem lower17 : ∀ b c : Fin 26, (17 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 17 b c := by decide +kernel
private theorem lower18 : ∀ b c : Fin 26, (18 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 18 b c := by decide +kernel
private theorem lower19 : ∀ b c : Fin 26, (19 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 19 b c := by decide +kernel
private theorem lower20 : ∀ b c : Fin 26, (20 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 20 b c := by decide +kernel
private theorem lower21 : ∀ b c : Fin 26, (21 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 21 b c := by decide +kernel
private theorem lower22 : ∀ b c : Fin 26, (22 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 22 b c := by decide +kernel
private theorem lower23 : ∀ b c : Fin 26, (23 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 23 b c := by decide +kernel
private theorem lower24 : ∀ b c : Fin 26, (24 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 24 b c := by decide +kernel
private theorem lower25 : ∀ b c : Fin 26, (25 : Fin 26) ≤ b → b ≤ c → 36 ≤ loss3 25 b c := by decide +kernel
private theorem ord_three (a b c : Fin 26) (h : a ≤ b) (k : b ≤ c) : 36 ≤ loss3 a b c := by
  fin_cases a
  · exact lower0 b c h k
  · exact lower1 b c h k
  · exact lower2 b c h k
  · exact lower3 b c h k
  · exact lower4 b c h k
  · exact lower5 b c h k
  · exact lower6 b c h k
  · exact lower7 b c h k
  · exact lower8 b c h k
  · exact lower9 b c h k
  · exact lower10 b c h k
  · exact lower11 b c h k
  · exact lower12 b c h k
  · exact lower13 b c h k
  · exact lower14 b c h k
  · exact lower15 b c h k
  · exact lower16 b c h k
  · exact lower17 b c h k
  · exact lower18 b c h k
  · exact lower19 b c h k
  · exact lower20 b c h k
  · exact lower21 b c h k
  · exact lower22 b c h k
  · exact lower23 b c h k
  · exact lower24 b c h k
  · exact lower25 b c h k
theorem three_lower (a b c : Fin 26) : 36 ≤ loss3 a b c := by
  have order : (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨ (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by omega
  rcases order with h|h|h|h|h|h
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three a b c h.1 h.2
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three a c b h.1 h.2
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three b a c h.1 h.2
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three b c a h.1 h.2
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three c a b h.1 h.2
  · simpa only [loss3,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm] using ord_three c b a h.1 h.2
theorem sharp_counts : loss1 0 = 135 ∧ loss2 0 1 = 81 ∧ loss3 0 17 23 = 36 := by decide +kernel

end PEqualNP.Research.PuncturedFlags

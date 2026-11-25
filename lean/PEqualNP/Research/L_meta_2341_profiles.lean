import PEqualNP.Research.L_meta_2341_data
namespace PEqualNP.Research.PuncturedFlags
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
def inter4 (a b c d : Fin 26) := column a &&& column b &&& column c &&& column d
def omit4 (a b c d : Fin 26) := 2^a.val ||| 2^b.val ||| 2^c.val ||| 2^d.val
private theorem four0 : ∀ b c d : Fin 26, (0 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 0 b c d = 0 ↔ omit4 0 b c d = 42074113 ∨ omit4 0 b c d = 8714) := by decide +kernel
private theorem four1 : ∀ b c d : Fin 26, (1 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 1 b c d = 0 ↔ omit4 1 b c d = 42074113 ∨ omit4 1 b c d = 8714) := by decide +kernel
private theorem four2 : ∀ b c d : Fin 26, (2 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 2 b c d = 0 ↔ omit4 2 b c d = 42074113 ∨ omit4 2 b c d = 8714) := by decide +kernel
private theorem four3 : ∀ b c d : Fin 26, (3 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 3 b c d = 0 ↔ omit4 3 b c d = 42074113 ∨ omit4 3 b c d = 8714) := by decide +kernel
private theorem four4 : ∀ b c d : Fin 26, (4 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 4 b c d = 0 ↔ omit4 4 b c d = 42074113 ∨ omit4 4 b c d = 8714) := by decide +kernel
private theorem four5 : ∀ b c d : Fin 26, (5 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 5 b c d = 0 ↔ omit4 5 b c d = 42074113 ∨ omit4 5 b c d = 8714) := by decide +kernel
private theorem four6 : ∀ b c d : Fin 26, (6 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 6 b c d = 0 ↔ omit4 6 b c d = 42074113 ∨ omit4 6 b c d = 8714) := by decide +kernel
private theorem four7 : ∀ b c d : Fin 26, (7 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 7 b c d = 0 ↔ omit4 7 b c d = 42074113 ∨ omit4 7 b c d = 8714) := by decide +kernel
private theorem four8 : ∀ b c d : Fin 26, (8 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 8 b c d = 0 ↔ omit4 8 b c d = 42074113 ∨ omit4 8 b c d = 8714) := by decide +kernel
private theorem four9 : ∀ b c d : Fin 26, (9 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 9 b c d = 0 ↔ omit4 9 b c d = 42074113 ∨ omit4 9 b c d = 8714) := by decide +kernel
private theorem four10 : ∀ b c d : Fin 26, (10 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 10 b c d = 0 ↔ omit4 10 b c d = 42074113 ∨ omit4 10 b c d = 8714) := by decide +kernel
private theorem four11 : ∀ b c d : Fin 26, (11 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 11 b c d = 0 ↔ omit4 11 b c d = 42074113 ∨ omit4 11 b c d = 8714) := by decide +kernel
private theorem four12 : ∀ b c d : Fin 26, (12 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 12 b c d = 0 ↔ omit4 12 b c d = 42074113 ∨ omit4 12 b c d = 8714) := by decide +kernel
private theorem four13 : ∀ b c d : Fin 26, (13 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 13 b c d = 0 ↔ omit4 13 b c d = 42074113 ∨ omit4 13 b c d = 8714) := by decide +kernel
private theorem four14 : ∀ b c d : Fin 26, (14 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 14 b c d = 0 ↔ omit4 14 b c d = 42074113 ∨ omit4 14 b c d = 8714) := by decide +kernel
private theorem four15 : ∀ b c d : Fin 26, (15 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 15 b c d = 0 ↔ omit4 15 b c d = 42074113 ∨ omit4 15 b c d = 8714) := by decide +kernel
private theorem four16 : ∀ b c d : Fin 26, (16 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 16 b c d = 0 ↔ omit4 16 b c d = 42074113 ∨ omit4 16 b c d = 8714) := by decide +kernel
private theorem four17 : ∀ b c d : Fin 26, (17 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 17 b c d = 0 ↔ omit4 17 b c d = 42074113 ∨ omit4 17 b c d = 8714) := by decide +kernel
private theorem four18 : ∀ b c d : Fin 26, (18 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 18 b c d = 0 ↔ omit4 18 b c d = 42074113 ∨ omit4 18 b c d = 8714) := by decide +kernel
private theorem four19 : ∀ b c d : Fin 26, (19 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 19 b c d = 0 ↔ omit4 19 b c d = 42074113 ∨ omit4 19 b c d = 8714) := by decide +kernel
private theorem four20 : ∀ b c d : Fin 26, (20 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 20 b c d = 0 ↔ omit4 20 b c d = 42074113 ∨ omit4 20 b c d = 8714) := by decide +kernel
private theorem four21 : ∀ b c d : Fin 26, (21 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 21 b c d = 0 ↔ omit4 21 b c d = 42074113 ∨ omit4 21 b c d = 8714) := by decide +kernel
private theorem four22 : ∀ b c d : Fin 26, (22 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 22 b c d = 0 ↔ omit4 22 b c d = 42074113 ∨ omit4 22 b c d = 8714) := by decide +kernel
private theorem four23 : ∀ b c d : Fin 26, (23 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 23 b c d = 0 ↔ omit4 23 b c d = 42074113 ∨ omit4 23 b c d = 8714) := by decide +kernel
private theorem four24 : ∀ b c d : Fin 26, (24 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 24 b c d = 0 ↔ omit4 24 b c d = 42074113 ∨ omit4 24 b c d = 8714) := by decide +kernel
private theorem four25 : ∀ b c d : Fin 26, (25 : Fin 26) ≤ b → b ≤ c → c ≤ d → (inter4 25 b c d = 0 ↔ omit4 25 b c d = 42074113 ∨ omit4 25 b c d = 8714) := by decide +kernel
private theorem ord_four (a b c d : Fin 26) (h : a ≤ b) (k : b ≤ c) (m : c ≤ d) : inter4 a b c d = 0 ↔ omit4 a b c d = 42074113 ∨ omit4 a b c d = 8714 := by
  fin_cases a
  · exact four0 b c d h k m
  · exact four1 b c d h k m
  · exact four2 b c d h k m
  · exact four3 b c d h k m
  · exact four4 b c d h k m
  · exact four5 b c d h k m
  · exact four6 b c d h k m
  · exact four7 b c d h k m
  · exact four8 b c d h k m
  · exact four9 b c d h k m
  · exact four10 b c d h k m
  · exact four11 b c d h k m
  · exact four12 b c d h k m
  · exact four13 b c d h k m
  · exact four14 b c d h k m
  · exact four15 b c d h k m
  · exact four16 b c d h k m
  · exact four17 b c d h k m
  · exact four18 b c d h k m
  · exact four19 b c d h k m
  · exact four20 b c d h k m
  · exact four21 b c d h k m
  · exact four22 b c d h k m
  · exact four23 b c d h k m
  · exact four24 b c d h k m
  · exact four25 b c d h k m
theorem profile_four (a b c d : Fin 26) : inter4 a b c d = 0 ↔ omit4 a b c d = 42074113 ∨ omit4 a b c d = 8714 := by
  by_cases h10 : b ≤ a
  · by_cases h20 : c ≤ b
    · by_cases h30 : d ≤ c
      · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d c b a (by omega) (by omega) (by omega)
      · by_cases h31 : d ≤ b
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c d b a (by omega) (by omega) (by omega)
        · by_cases h32 : d ≤ a
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c b d a (by omega) (by omega) (by omega)
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c b a d (by omega) (by omega) (by omega)
    · by_cases h21 : c ≤ a
      · by_cases h30 : d ≤ b
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d b c a (by omega) (by omega) (by omega)
        · by_cases h31 : d ≤ c
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b d c a (by omega) (by omega) (by omega)
          · by_cases h32 : d ≤ a
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b c d a (by omega) (by omega) (by omega)
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b c a d (by omega) (by omega) (by omega)
      · by_cases h30 : d ≤ b
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d b a c (by omega) (by omega) (by omega)
        · by_cases h31 : d ≤ a
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b d a c (by omega) (by omega) (by omega)
          · by_cases h32 : d ≤ c
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b a d c (by omega) (by omega) (by omega)
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four b a c d (by omega) (by omega) (by omega)
  · by_cases h20 : c ≤ a
    · by_cases h30 : d ≤ c
      · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d c a b (by omega) (by omega) (by omega)
      · by_cases h31 : d ≤ a
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c d a b (by omega) (by omega) (by omega)
        · by_cases h32 : d ≤ b
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c a d b (by omega) (by omega) (by omega)
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four c a b d (by omega) (by omega) (by omega)
    · by_cases h21 : c ≤ b
      · by_cases h30 : d ≤ a
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d a c b (by omega) (by omega) (by omega)
        · by_cases h31 : d ≤ c
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a d c b (by omega) (by omega) (by omega)
          · by_cases h32 : d ≤ b
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a c d b (by omega) (by omega) (by omega)
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a c b d (by omega) (by omega) (by omega)
      · by_cases h30 : d ≤ a
        · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four d a b c (by omega) (by omega) (by omega)
        · by_cases h31 : d ≤ b
          · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a d b c (by omega) (by omega) (by omega)
          · by_cases h32 : d ≤ c
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a b d c (by omega) (by omega) (by omega)
            · simpa only [inter4,omit4,Nat.and_assoc,Nat.and_left_comm,Nat.and_comm,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using ord_four a b c d (by omega) (by omega) (by omega)

end PEqualNP.Research.PuncturedFlags

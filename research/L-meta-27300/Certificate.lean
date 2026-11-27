import Signature
namespace PEqualNP.Research.Permanent27300
def certPrice (a : BitVec 8) : ℕ := ((0x9351d49c7254a45244636ec4dc52592d92d4e52dc8e46a475d5144d350b96d7246e3292b6d75d96595cb6d75d9654d369ab2caebb6d8ecb2caebb6d49171b923b6c66269a8a2aeb91391c8d9b1ab64b64b228da95b70a922912b238d2ae2690 : ℕ) >>> (3*a.toNat)) &&& 7
def bucket : ℕ → List (BitVec 8)
  | 0 => [0, 255]
  | 1 => [25, 52, 78, 92, 163, 177, 203, 230]
  | 2 => [1, 2, 4, 8, 9, 16, 17, 20, 24, 32, 36, 48, 61, 68, 70, 72, 74, 76, 93, 94, 95, 124, 126, 129, 131, 160, 161, 162, 179, 181, 183, 185, 187, 194, 207, 219, 223, 231, 235, 238, 239, 246, 247, 251, 253, 254]
  | 3 => [3, 6, 10, 12, 27, 28, 29, 33, 34, 49, 53, 54, 57, 60, 64, 66, 73, 75, 79, 84, 88, 89, 91, 100, 102, 110, 116, 118, 125, 127, 128, 130, 137, 139, 145, 153, 155, 164, 166, 167, 171, 176, 180, 182, 189, 191, 195, 198, 201, 202, 206, 221, 222, 226, 227, 228, 243, 245, 249, 252]
  | 4 => [5, 11, 13, 14, 18, 19, 21, 22, 23, 26, 31, 35, 37, 38, 40, 41, 44, 45, 50, 55, 56, 58, 59, 62, 63, 69, 71, 77, 80, 85, 86, 87, 90, 104, 106, 108, 111, 120, 122, 133, 135, 144, 147, 149, 151, 165, 168, 169, 170, 175, 178, 184, 186, 192, 193, 196, 197, 199, 200, 205, 210, 211, 214, 215, 217, 218, 220, 224, 229, 232, 233, 234, 236, 237, 241, 242, 244, 250]
  | _ => []
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
theorem cap : ∀ a : BitVec 8, certPrice a ≤ 5 := by decide +kernel
theorem listed : ∀ a : BitVec 8, certPrice a < 5 → a ∈ bucket (certPrice a) := by decide +kernel
def sums (a b : BitVec 8) : Prop := certPrice (a &&& b) ≤ certPrice a + certPrice b ∧
    certPrice (a ||| b) ≤ certPrice a + certPrice b
instance (a b : BitVec 8) : Decidable (sums a b) := by unfold sums; infer_instance
def validPair (i j : ℕ) := (bucket i).all fun a => (bucket j).all fun b => decide (sums a b)
theorem cheaper : ((List.range 5).all fun i => (List.range 5).all fun j =>
    decide (5 ≤ i+j) || validPair i j) = true := by decide +kernel
theorem combine (a b : BitVec 8) : sums a b := by
  by_cases h : 5 ≤ certPrice a + certPrice b
  · exact ⟨(cap _).trans h,(cap _).trans h⟩
  have ha : certPrice a < 5 := by omega
  have hb : certPrice b < 5 := by omega
  have row := List.all_eq_true.mp cheaper (certPrice a) (List.mem_range.mpr ha)
  have chk := List.all_eq_true.mp row (certPrice b) (List.mem_range.mpr hb)
  have ok : validPair (certPrice a) (certPrice b) = true := by simpa [h] using chk
  have r := List.all_eq_true.mp ok a (listed a ha)
  exact of_decide_eq_true (List.all_eq_true.mp r b (listed b hb))
theorem complement : ∀ a : BitVec 8, certPrice (~~~a) = certPrice a := by decide +kernel
end PEqualNP.Research.Permanent27300

import PEqualNP.Research.AffineMatrix
namespace PEqualNP.Research.AffineRectangleCover
open Finset
def refData : Array (Nat × Nat) := #[(17098368,50373122), (65602,681095837), (7090692,8654337), (27591456,168050756), (302444,537920592), (100880,543434860), (18886834,272929024), (6947366,159384616), (13638217,269092992), (18877445,354762824), (542912,588450057), (4326416,75707626), (17960960,107529610), (8560644,86548786), (1114280,139577520), (795673,604045446), (25690584,137367553), (12599584,311955554), (6324235,222433808), (743438,604520449), (1327361,12804870)]
def rowMask (k : Fin 21) := refData[k.val]!.1
def colMask (k : Fin 21) := refData[k.val]!.2
def box (k : Fin 21) : Box := (univ.filter (fun i => (rowMask k).testBit i.val),
    univ.filter (fun j => (colMask k).testBit j.val))
def ref := (List.finRange 21).map box
def selected : Array (Fin 21) := #[0, 15, 15, 9, 18, 0, 9, 8, 20, 18, 0, 8, 18, 20, 9, 0, 9, 8, 9, 8, 0, 9, 18, 20, 9, 0, 9, 18, 8, 15, 1, 0, 1, 1, 1, 7, 0, 1, 6, 1, 7, 0, 1, 1, 19, 1, 0, 18, 6, 1, 1, 0, 6, 1, 7, 0, 18, 1, 6, 1, 2, 13, 0, 7, 4, 7, 4, 0, 13, 2, 2, 2, 0, 13, 9, 13, 9, 0, 2, 13, 4, 9, 0, 2, 7, 0, 9, 7, 9, 4, 16, 15, 15, 0, 4, 14, 4, 8, 0, 18, 4, 8, 16, 0, 14, 14, 14, 8, 0, 8, 4, 16, 14, 0, 18, 0, 15, 14, 8, 4, 16, 11, 5, 5, 0, 5, 5, 11, 6, 0, 11, 5, 6, 5, 0, 6, 11, 11, 5, 0, 16, 5, 5, 11, 0, 0, 11, 16, 6, 5, 0, 17, 3, 7, 4, 7, 3, 14, 6, 0, 4, 14, 6, 0, 3, 6, 14, 0, 3, 17, 4, 0, 6, 7, 7, 3, 0, 3, 6, 4, 1, 0, 1, 1, 1, 0, 4, 1, 10, 1, 4, 8, 1, 1, 0, 1, 10, 8, 0, 1, 1, 16, 0, 1, 10, 10, 0, 1, 8, 1, 10, 0, 0, 10, 14, 14, 0, 14, 6, 0, 0, 10, 6, 0, 14, 0, 10, 10, 6, 0, 10, 16, 6, 0, 0, 0, 0, 14, 6, 10, 16, 17, 3, 0, 4, 17, 3, 0, 20, 20, 4, 0, 16, 20, 3, 0, 20, 20, 3, 17, 4, 16, 20, 17, 0, 3, 0, 3, 17, 4, 2, 0, 3, 5, 0, 5, 3, 8, 0, 0, 2, 2, 0, 0, 3, 0, 0, 8, 2, 8, 0, 5, 5, 2, 0, 0, 0, 3, 8, 5, 0, 0, 15, 9, 4, 11, 4, 11, 0, 0, 4, 0, 11, 0, 9, 0, 9, 11, 9, 0, 4, 9, 0, 11, 0, 0, 9, 0, 9, 4, 10, 0, 5, 5, 4, 5, 4, 8, 10, 0, 4, 5, 0, 5, 9, 0, 9, 8, 5, 8, 4, 5, 5, 0, 9, 10, 9, 0, 8, 4, 2, 12, 0, 12, 4, 0, 4, 8, 6, 2, 2, 2, 6, 0, 12, 6, 0, 8, 2, 8, 4, 12, 6, 2, 0, 12, 12, 0, 6, 4, 2, 0, 15, 0, 13, 13, 0, 15, 6, 0, 2, 2, 6, 0, 0, 0, 15, 0, 2, 13, 0, 13, 6, 2, 0, 0, 13, 0, 6, 15, 10, 0, 20, 10, 0, 17, 17, 0, 10, 0, 0, 10, 17, 0, 19, 0, 10, 10, 0, 17, 10, 0, 20, 17, 0, 0, 19, 0, 17, 10, 0, 0, 5, 5, 4, 5, 4, 0, 13, 0, 4, 5, 18, 0, 0, 0, 0, 18, 5, 13, 4, 5, 5, 0, 0, 0, 13, 18, 0, 4, 1, 0, 1, 1, 1, 5, 3, 1, 0, 1, 0, 5, 1, 1, 3, 1, 14, 0, 3, 1, 1, 5, 5, 1, 0, 3, 19, 1, 0, 1, 19, 11, 0, 7, 13, 7, 11, 11, 12, 0, 7, 0, 11, 11, 12, 12, 11, 11, 0, 12, 0, 12, 12, 7, 7, 12, 11, 7, 0, 19, 2, 0, 3, 0, 4, 0, 3, 15, 20, 0, 2, 2, 0, 0, 3, 0, 15, 20, 2, 0, 4, 0, 20, 2, 0, 0, 15, 3, 0, 4, 2, 15, 15, 7, 0, 7, 0, 15, 10, 2, 2, 2, 16, 0, 19, 0, 10, 10, 2, 19, 10, 16, 0, 2, 7, 10, 15, 7, 0, 10, 0, 12, 20, 12, 14, 14, 0, 8, 12, 20, 12, 8, 0, 20, 12, 12, 14, 8, 0, 8, 14, 12, 12, 20, 0, 12, 12, 14, 8, 0, 2, 0, 3, 7, 18, 7, 3, 0, 6, 2, 2, 2, 6, 0, 3, 6, 9, 18, 2, 0, 0, 9, 6, 2, 7, 3, 9, 3, 6, 0, 2, 11, 0, 7, 18, 7, 11, 8, 0, 2, 2, 2, 11, 11, 0, 0, 11, 8, 2, 8, 17, 0, 18, 2, 7, 17, 11, 7, 8, 0, 16, 13, 3, 0, 13, 13, 3, 8, 13, 0, 0, 8, 16, 13, 3, 13, 0, 8, 3, 8, 16, 13, 0, 17, 13, 3, 13, 3, 8, 0, 16, 0, 3, 9, 0, 0, 3, 12, 6, 0, 12, 0, 6, 0, 3, 0, 9, 0, 3, 12, 16, 9, 6, 0, 0, 0, 9, 3, 6, 0]
def pick (p : P) (l : L) : Fin 21 := selected[30*p.val+l.val]!
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
theorem ref_safe : ∀ (k : Fin 21) (p : P) (l : L), (rowMask k).testBit p.val = true →
    (colMask k).testBit l.val = true → zero p l = true := by decide +kernel
theorem pick_hits : ∀ (p : P) (l : L), zero p l = true →
    (rowMask (pick p l)).testBit p.val && (colMask (pick p l)).testBit l.val := by decide +kernel
theorem reference_length : ref.length = 21 := by simp [ref]
theorem reference_sound : ∀ b ∈ ref, ∀ p ∈ b.1, ∀ l ∈ b.2,
    (rows.getD p.val 0).testBit l.val = false := by
  intro b hb p hp l hl
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hb
  simpa [zero] using ref_safe k p l (mem_filter.mp hp).2 (mem_filter.mp hl).2
theorem reference_complete : ∀ p : P, ∀ l : L, (rows.getD p.val 0).testBit l.val = false →
    ∃ b ∈ ref, p ∈ b.1 ∧ l ∈ b.2 := by
  intro p l h
  have hh := pick_hits p l (by unfold zero; rw [h]; rfl)
  simp only [Bool.and_eq_true] at hh
  exact ⟨box (pick p l), List.mem_map.mpr ⟨_,List.mem_finRange _,rfl⟩,
     mem_filter.mpr ⟨mem_univ _,hh.1⟩,mem_filter.mpr ⟨mem_univ _,hh.2⟩⟩
theorem upper : ∃ B : List Box, B.length ≤ 21 ∧
    (∀ b ∈ B, ∀ p ∈ b.1, ∀ l ∈ b.2, (rows.getD p.val 0).testBit l.val = false) ∧
    ∀ p : P, ∀ l : L, (rows.getD p.val 0).testBit l.val = false →
    ∃ b ∈ B, p ∈ b.1 ∧ l ∈ b.2 := ⟨ref, reference_length.le, reference_sound, reference_complete⟩
end PEqualNP.Research.AffineRectangleCover

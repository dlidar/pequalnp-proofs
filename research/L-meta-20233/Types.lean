import Full
namespace PlaneMask
instance (r c : Byte) : Decidable (form r c) := by unfold form; infer_instance
theorem listed_forms : allW.all (fun w => decide (form w.r w.c)) = true := by decide +kernel
def unitByte (i : Fin 8) : Byte := ⟨2^i.val,by fin_cases i <;> decide⟩
theorem left_unit : ∀ i, (allowed (unitByte i)).getLsbD 0 = true := by decide +kernel
theorem right_unit : ∀ i, (allowed 0).getLsbD (unitByte i).val = true := by decide +kernel
theorem paired : ∀ i j : Fin 8, (14466700110149527140 : Nat).testBit (8*i.val+j.val) = false →
    (allowed (unitByte i)).getLsbD (unitByte j).val = true := by decide +kernel

theorem one_bit_splits (r c : Byte) : Fits r c ↔ form r c := by
  constructor
  · intro h
    obtain ⟨w,hw,rfl,rfl⟩ := (exact_list _ _).mp h
    exact of_decide_eq_true (List.all_eq_true.mp listed_forms _ hw)
  · intro h
    apply (exact_class r c).mpr
    rcases h with ⟨hr,hc⟩ | ⟨hr,hc⟩ | ⟨i,hr,hc⟩ | ⟨j,hr,hc⟩ | ⟨i,j,hr,hc,hij⟩
    · have a : r = 0 := Fin.ext hr
      have b : c = 0 := Fin.ext hc
      subst r; subst c; decide
    · have a : r = 255 := Fin.ext hr
      have b : c = 255 := Fin.ext hc
      subst r; subst c; decide
    · have a : r = unitByte i := Fin.ext hr
      rw [a,hc]; exact left_unit i
    · have a : r = 0 := Fin.ext hr
      have b : c = unitByte j := Fin.ext hc
      rw [a,b]; exact right_unit j
    · have a : r = unitByte i := Fin.ext hr
      have b : c = unitByte j := Fin.ext hc
      rw [a,b]; exact paired i j hij
end PlaneMask
#print axioms PlaneMask.one_bit_splits

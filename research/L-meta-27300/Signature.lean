import Mathlib
namespace PEqualNP.Research.Permanent27300

def signature (f : Fin 8 → Bool) : BitVec 8 :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn ..)
theorem signature_bit (f : Fin 8 → Bool) (i : Fin 8) : (signature f).getLsbD i.val = f i := by
  simp only [signature,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  fin_cases i <;> rfl
theorem sig_and (f g : Fin 8 → Bool) :
    signature (fun i => f i && g i) = signature f &&& signature g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [signature_bit _ ⟨i,hi⟩,BitVec.getLsbD_and,signature_bit _ ⟨i,hi⟩,signature_bit _ ⟨i,hi⟩]
theorem sig_or (f g : Fin 8 → Bool) :
    signature (fun i => f i || g i) = signature f ||| signature g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [signature_bit _ ⟨i,hi⟩,BitVec.getLsbD_or,signature_bit _ ⟨i,hi⟩,signature_bit _ ⟨i,hi⟩]
theorem sig_not (f : Fin 8 → Bool) :
    signature (fun i => !(f i)) = ~~~(signature f) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [signature_bit _ ⟨i,hi⟩,BitVec.getLsbD_not]
  rw [signature_bit _ ⟨i,hi⟩]
  simp [hi]

end PEqualNP.Research.Permanent27300

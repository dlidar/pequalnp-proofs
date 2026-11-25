import PEqualNP.Research.L_meta_2341_counts
import PEqualNP.Research.L_meta_2341_semantics
namespace PEqualNP.Research.PuncturedFlags

def negativeCount (f : Factor) := (List.range 234).countP (fun j => f (neg (Fin.ofNat 234 j)))

theorem pop_common (ds : List (Fin 26)) :
    pop 5 (common ds) = negativeCount (projected ds) := by
  rw [pop_correct]
  change (List.range (234+22)).countP (common ds).testBit = _
  rw [List.range_add,List.countP_append,List.countP_map]
  have tail0 : (List.range 22).countP (fun j => (common ds).testBit (234+j)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro j _
    simp [Nat.testBit_lt_two_pow ((common_bound ds).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 234 ≤ 234+j)))]
  change _ + (List.range 22).countP (fun j => (common ds).testBit (234+j)) = _
  rw [tail0,Nat.add_zero]
  apply List.countP_congr
  intro j hj
  have h := List.mem_range.mp hj
  have eq : Fin.ofNat 234 j = (⟨j,h⟩ : Fin 234) := Fin.ext (Nat.mod_eq_of_lt h)
  change _ ↔ projected ds (neg (Fin.ofNat 234 j)) = true
  rw [eq]
  exact Bool.eq_iff_iff.mp (common_bit ds ⟨j,h⟩)

theorem loss_le (fs : List (Fin 26 × Factor)) (good : ∀ a ∈ fs, Mon a.2 ∧ Omits a.2 a.1)
    (positive : Accepts (product fs)) :
    negativeCount (projected (fs.map Prod.fst)) ≤ negativeCount (product fs) := by
  apply List.countP_mono_left
  intro j _ yes
  apply List.all_eq_true.mpr
  intro a ha
  have acc : Accepts a.2 := fun i => List.all_eq_true.mp (positive i) a ha
  exact project_least (good a ha).1 (good a ha).2 acc _
    (List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨a,ha,rfl⟩))

theorem minimum_errors (a b c : Fin 26) :
    135 ≤ negativeCount (projected [a]) ∧ 81 ≤ negativeCount (projected [a,b]) ∧
      36 ≤ negativeCount (projected [a,b,c]) := by
  simp only [←pop_common,common,List.foldr_cons,List.foldr_nil,trim]
  exact ⟨one_lower a,two_lower a b,by simpa only [loss3,Nat.and_assoc] using three_lower a b c⟩

theorem attained_errors :
    negativeCount (projected [0]) = 135 ∧ negativeCount (projected [0,1]) = 81 ∧
      negativeCount (projected [0,17,23]) = 36 := by
  simpa only [←pop_common,common,List.foldr_cons,List.foldr_nil,trim,loss1,loss2,loss3,Nat.and_assoc] using sharp_counts

end PEqualNP.Research.PuncturedFlags

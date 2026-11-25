import PEqualNP.Research.L_meta_2341_projection
import PEqualNP.Research.L_meta_2341_columns

namespace PEqualNP.Research.PuncturedFlags
theorem product_necessary (fs : List (Fin 26 × Factor))
    (good : ∀ a ∈ fs, Mon a.2 ∧ Omits a.2 a.1)
    (positive : Accepts (product fs)) (negative : Rejects (product fs)) :
    common (fs.map Prod.fst) = 0 := by
  apply (zero_iff _).mpr
  intro j; apply Bool.eq_false_iff.mpr; intro bad
  have yes : product fs (neg j) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    have acc : Accepts a.2 := fun i => List.all_eq_true.mp (positive i) a ha
    exact project_least (good a ha).1 (good a ha).2 acc _
      (List.all_eq_true.mp bad _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
  exact Bool.noConfusion ((negative j).symm.trans yes)

theorem projected_exact (ds : List (Fin 26)) :
    Accepts (projected ds) ∧ (Rejects (projected ds) ↔ common ds = 0) :=
  ⟨fun i => List.all_eq_true.mpr (fun d _ => project_accepts d i),(zero_iff ds).symm⟩

theorem trim (a : Fin 26) : column a &&& (2^234-1) = column a := by
  exact (by decide +kernel : ∀ a : Fin 26, column a &&& (2^234-1) = column a) a

theorem least_separators : common pointStar = 0 ∧ common lineStar = 0 := by decide +kernel

theorem sharp_examples :
    (Accepts (projected pointStar) ∧ Rejects (projected pointStar)) ∧
    (Accepts (projected lineStar) ∧ Rejects (projected lineStar)) :=
  ⟨⟨(projected_exact _).1,(projected_exact _).2.mpr least_separators.1⟩,
   ⟨(projected_exact _).1,(projected_exact _).2.mpr least_separators.2⟩⟩


end PEqualNP.Research.PuncturedFlags

import PEqualNP.Research.L_meta_2341_semantics
import PEqualNP.Research.L_meta_2341_profiles

namespace PEqualNP.Research.PuncturedFlags

theorem triple_obstruction : ∀ a b c : Fin 26, common [a,b,c] ≠ 0 := by decide +kernel

theorem exact_four (a b c d : Fin 26) : common [a,b,c,d] = 0 ↔
    omissions [a,b,c,d] = omissions pointStar ∨ omissions [a,b,c,d] = omissions lineStar := by
  have pp : omissions pointStar = 42074113 := by decide +kernel
  have ll : omissions lineStar = 8714 := by decide +kernel
  rw [pp,ll]
  simpa only [common,omissions,List.foldr_cons,List.foldr_nil,trim,Nat.or_zero,inter4,omit4,
    Nat.and_assoc,Nat.or_assoc] using profile_four a b c d

theorem omission_mem (ds : List (Fin 26)) (v : Fin 26) :
    (omissions ds).testBit v.val = true ↔ v ∈ ds := by
  induction ds with
  | nil => simp [omissions]
  | cons a as ih =>
    change (2^a.val ||| omissions as).testBit v.val = true ↔ _
    simp only [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    simp [Fin.ext_iff,eq_comm]

theorem distinct_if_feasible (a b c d : Fin 26) (h : common [a,b,c,d] = 0) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d := by
  have h4 := (zero_iff _).mp h
  have h3 := triple_obstruction b c d
  have lift (same : a=b ∨ a=c ∨ a=d) : common [b,c,d] = 0 := by
    apply (zero_iff _).mpr
    intro j; apply Bool.eq_false_iff.mpr
    intro yes
    have sat := List.all_eq_true.mp yes
    have h' : [a,b,c,d].all (fun v => project v (neg j)) = true := by
      apply List.all_eq_true.mpr
      intro v hv; apply sat
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
      rcases hv with rfl|rfl|rfl|rfl <;> tauto
    exact Bool.noConfusion ((h4 j).symm.trans h')
  exact ⟨fun e => h3 (lift (Or.inl e)),fun e => h3 (lift (Or.inr (Or.inl e))),
    fun e => h3 (lift (Or.inr (Or.inr e)))⟩

theorem unique_first (a e b c d : Fin 26) (x : common [a,b,c,d]=0) (y : common [e,b,c,d]=0) : a=e := by
  have sep : ∀v : Fin 26, v ∈ pointStar → v ∉ lineStar := by decide +kernel
  have eq : omissions [a,b,c,d] = omissions [e,b,c,d] := by
    have xb := (omission_mem [a,b,c,d] b).mpr (by simp)
    have yb := (omission_mem [e,b,c,d] b).mpr (by simp)
    rcases (exact_four a b c d).mp x with h|h <;> rcases (exact_four e b c d).mp y with k|k
    · exact h.trans k.symm
    · rw [h] at xb; rw [k] at yb
      exact False.elim (sep b ((omission_mem _ _).mp xb) ((omission_mem _ _).mp yb))
    · rw [h] at xb; rw [k] at yb
      exact False.elim (sep b ((omission_mem _ _).mp yb) ((omission_mem _ _).mp xb))
    · exact h.trans k.symm
  have has := (omission_mem [a,b,c,d] a).mpr (by simp)
  rw [eq] at has
  have mem := (omission_mem [e,b,c,d] a).mp has
  have ne := distinct_if_feasible _ _ _ _ x
  simpa [ne.1,ne.2.1,ne.2.2] using mem

/-- A factor in a successful four-factor product can omit only its designated
coordinate. Any other possible omission yields a second feasible tuple. -/
theorem factor_rigidity (f g h k : Factor) (a e b c d : Fin 26)
    (mf : Mon f) (mg : Mon g) (mh : Mon h) (mk : Mon k)
    (fa : Omits f a) (fe : Omits f e) (gb : Omits g b) (hc : Omits h c) (kd : Omits k d)
    (hp : ∀ i, (f (pos i) && g (pos i) && h (pos i) && k (pos i)) = true)
    (hn : ∀ j, (f (neg j) && g (neg j) && h (neg j) && k (neg j)) = false) : a=e := by
  have force (i : Fin 26) (fi : Omits f i) : common [i,b,c,d] = 0 := by
    let fs : List (Fin 26 × Factor) := [(i,f),(b,g),(c,h),(d,k)]
    apply product_necessary fs
    · intro pair hx
      simp only [fs,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact ⟨mf,fi⟩
      · exact ⟨mg,gb⟩
      · exact ⟨mh,hc⟩
      · exact ⟨mk,kd⟩
    · intro j; simpa [fs,product,Bool.and_assoc] using hp j
    · intro j; simpa [fs,product,Bool.and_assoc] using hn j
  exact unique_first a e b c d (force a fa) (force e fe)

end PEqualNP.Research.PuncturedFlags

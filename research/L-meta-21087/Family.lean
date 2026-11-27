import Support

open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Support

namespace Mask114591Family

theorem oneEach_bit {n m : Nat} (u : Fin n) (v : Fin m) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append]
  simp only [List.length_ofFn, List.getElem?_ofFn]
  split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
  have hne : i ≠ u.val := by omega
  have he : i - n = v.val ↔ i = n + v.val := by omega
  simp [hne,he]

theorem essential_support {n m : Nat} (A : Fin n → Fin m → Bool)
    (rows : ∀ u, ∃ v u', A u v = true ∧ A u' v = false)
    (cols : ∀ v, ∃ u v', A u v = true ∧ A u v' = false)
    (C : Circuit) (hc : Monotone2 C) (hr : Represents A C) :
    n + m ≤ C.size + 1 := by
  obtain ⟨s,hs,mono⟩ := monotone_support C hc (n+m)
  have allInputs : Finset.range (n+m) ⊆ s := by
    intro i hi
    have hb := Finset.mem_range.mp hi
    by_contra hnot
    by_cases h : i < n
    · let u : Fin n := ⟨i,h⟩
      obtain ⟨v,u',hon,hoff⟩ := rows u
      have cmp : agrees (oneEach u v) (oneEach u' v) s := by
        intro j hj
        have hne : j ≠ u.val := fun eq => hnot (show u.val ∈ s from eq ▸ hj)
        rw [oneEach_bit,oneEach_bit]
        simp [hne] <;> tauto
      have he := mono _ _ (by simp [oneEach]) (by simp [oneEach]) cmp ((hr u v).trans hon)
      rw [hr u' v, hoff] at he
      contradiction
    · let v : Fin m := ⟨i-n,by omega⟩
      obtain ⟨u,v',hon,hoff⟩ := cols v
      have hv : n + v.val = i := by dsimp [v]; omega
      have cmp : agrees (oneEach u v) (oneEach u v') s := by
        intro j hj
        have hne : j ≠ n + v.val := fun eq => hnot ((eq.trans hv) ▸ hj)
        rw [oneEach_bit,oneEach_bit]
        simp [hne] <;> tauto
      have he := mono _ _ (by simp [oneEach]) (by simp [oneEach]) cmp ((hr u v).trans hon)
      rw [hr u v', hoff] at he
      contradiction
  simpa using (Finset.card_le_card allInputs).trans hs

def base (u : Fin 4) (v : Fin 5) := (114591 : Nat).testBit (5*u.val + v.val)

def project {k : Nat} (v : Fin (5+k)) : Fin 5 :=
  if h : v.val < 5 then ⟨v.val,h⟩ else 2

def clone (k : Nat) (u : Fin 4) (v : Fin (5+k)) := base u (project v)

theorem project_onto (k : Nat) : Function.Surjective (@project k) := by
  intro v
  exact ⟨⟨v.val,by omega⟩,by simp [project,v.isLt]⟩

theorem cloned_lower (k : Nat) (C : Circuit) (hc : Monotone2 C)
    (hr : Represents (clone k) C) : k + 8 ≤ C.size := by
  have rows : ∀ u, ∃ v u', base u v = true ∧ base u' v = false := by decide
  have cols : ∀ v, ∃ u v', base u v = true ∧ base u v' = false := by decide
  have h := essential_support (clone k) (fun u => by
    obtain ⟨v,u',h,h'⟩ := rows u
    obtain ⟨w,hw⟩ := project_onto k v
    exact ⟨w,u',by simpa [clone,hw] using h,by simpa [clone,hw] using h'⟩)
    (fun v => by
      obtain ⟨u,v',h,h'⟩ := cols (project v)
      obtain ⟨w,hw⟩ := project_onto k v'
      exact ⟨u,w,h,by simpa [clone,hw] using h'⟩) C hc hr
  omega

end Mask114591Family
#print axioms Mask114591Family.essential_support
#print axioms Mask114591Family.cloned_lower

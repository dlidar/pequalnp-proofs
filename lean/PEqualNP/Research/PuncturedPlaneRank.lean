import PEqualNP.Research.PuncturedPlaneCut
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace PEqualNP.Research.PuncturedPlaneCut
open Finset
abbrev Key := ↥(messages 21 [])
abbrev Side := Nat → Bool

noncomputable def rowInput (a : Key) : Side := representative (by simp) a
def complementInput (a : Key) : Side := fun l => !(a.val.testBit l)

theorem row_key (a : Key) : neighborhood (rowInput a) 21 = a.val :=
  representative_eq (n:=21) (hidden:=[]) (by simp) a

theorem zero_diagonal (a : Key) : posted (input 21 [] (rowInput a) (complementInput a)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨j,_,_,yes,no⟩ := (posted_restricted (by decide : 21≤21) [] _ _).mp hit
  rw [row_key] at yes
  simp [complementInput,yes] at no

theorem zero_implies_le (a b : Key)
    (hz : posted (input 21 [] (rowInput a) (complementInput b)) = false) : a.val ≤ b.val := by
  have hb : a.val < 2^21 := row_key a ▸ neighborhood_bound (rowInput a) 21
  have eq : a.val &&& b.val = a.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases ha : a.val.testBit j <;> simp
    by_contra! h
    have hj : j<21 := by
      by_contra! far
      have z := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) far))
      simp [ha] at z
    have hit := (posted_restricted (by decide : 21≤21) [] (rowInput a) (complementInput b)).mpr
      ⟨j,hj,by simp,by simpa [row_key] using ha,by simpa [complementInput] using h⟩
    simp [hz] at hit
  exact eq ▸ Nat.and_le_right

def zeroRow (K : Type*) [Field K] (x : Side) (y : Side) : K :=
  if posted (input 21 [] x y) then 0 else 1

theorem independent_zero_rows (K : Type*) [Field K] :
    LinearIndependent K (fun a : Key => zeroRow K (rowInput a)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g h a
  suffices all : ∀ n, ∀ b : Key, b.val = n → g b = 0 from all _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro b hb
    have v := congrFun h (complementInput b)
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at v
    rw [Finset.sum_eq_single b] at v
    · simpa [zeroRow,zero_diagonal] using v
    · intro c _ ne
      cases hc : posted (input 21 [] (rowInput c) (complementInput b)) with
      | true => simp [zeroRow,hc]
      | false =>
        have le := zero_implies_le c b hc
        have neq : c.val ≠ b.val := fun e => ne (Subtype.ext e)
        rw [ih c.val (by omega) c rfl,zero_mul]
    · simp

theorem separated_products_lower (K : Type*) [Field K] {k : Nat}
    (A B : Fin k → Side → K)
    (compute : ∀ x y, zeroRow K x y = ∑ i, A i x * B i y) : 24925 ≤ k := by
  classical
  have lin : LinearIndependent K (fun a : Key => fun i : Fin k => A i (rowInput a)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply (Fintype.linearIndependent_iff.mp (independent_zero_rows K)) g
    funext y
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,compute,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have z := congrFun hg i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at z
    rw [z,zero_mul]
  have bound := lin.fintype_card_le_finrank
  simpa [Key,full_count] using bound

theorem separated_products_upper (K : Type*) [Field K] :
    ∃ A B : Key → Side → K, ∀ x y, zeroRow K x y = ∑ a, A a x * B a y := by
  classical
  let key (x : Side) : Key := ⟨visible 21 [] x,(mem_messages [] (by simp)).mpr ⟨x,rfl⟩⟩
  refine ⟨fun a x => if a=key x then 1 else 0,fun a => zeroRow K (rowInput a),?_⟩
  intro x y
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have same := (indistinguishable (by decide : 21≤21) [] (by simp) x (rowInput (key x))).mpr
    (representative_eq (n:=21) (hidden:=[]) (by simp) (key x)).symm
  simp [zeroRow,same y]

end PEqualNP.Research.PuncturedPlaneCut

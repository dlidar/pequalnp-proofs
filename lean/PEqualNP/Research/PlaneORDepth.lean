import Mathlib

namespace PEqualNP.Research.PlaneORDepth
open Finset
abbrev Bit := Fin 42
abbrev Input := Bit → Bool

inductive Expr where
  | var (i : Bit) | lit (v : Bool) | conj (f g : Expr) | disj (f g : Expr)

def eval (x : Input) : Expr → Bool
  | .var i => x i | .lit v => v
  | .conj f g => eval x f && eval x g | .disj f g => eval x f || eval x g

def depth : Expr → ℕ
  | .var _ | .lit _ => 0
  | .conj f g => max (depth f) (depth g)
  | .disj f g => max (depth f) (depth g) + 1

/-- One zero-certificate per rejecting assignment, counting only binary OR layers. -/
theorem certificate (f : Expr) (x : Input) (h : eval x f = false) :
    ∃ S : Finset Bit, S.card ≤ 2^depth f ∧ (∀ i ∈ S, x i = false) ∧
      ∀ y : Input, (∀ i ∈ S, y i = false) → eval y f = false := by
  induction f with
  | var i => exact ⟨{i},by simp [depth],by simpa [eval] using h,by simp [eval]⟩
  | lit v => exact ⟨∅,by simp,by simp,fun _ _ => h⟩
  | conj f g ih jh =>
    rcases Bool.and_eq_false_iff.mp h with l|r
    · obtain ⟨S,n,z,k⟩ := ih l
      exact ⟨S,n.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..)),z,
        fun y hy => by simp [eval,k y hy]⟩
    · obtain ⟨S,n,z,k⟩ := jh r
      exact ⟨S,n.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..)),z,
        fun y hy => by simp [eval,k y hy]⟩
  | disj f g ih jh =>
    obtain ⟨l,r⟩ := Bool.or_eq_false_iff.mp h
    obtain ⟨S,n,z,k⟩ := ih l
    obtain ⟨T,m,t,u⟩ := jh r
    have a := n.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left (depth f) (depth g)))
    have b := m.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_right (depth f) (depth g)))
    refine ⟨S ∪ T,?_,fun i hi => (mem_union.mp hi).elim (z i) (t i),?_⟩
    · simp only [depth,pow_succ]; have := card_union_le S T;omega
    · intro y hy; simp [eval,k y (fun i h => hy i (mem_union_left T h)),u y (fun i h => hy i (mem_union_right S h))]

def adjacent (p l : Fin 21) := ([((p:ℕ)+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val
def graph (x : Input) : Bool := decide (∃ p l : Fin 21, adjacent p l ∧ x (Fin.castAdd 21 p) ∧ x (Fin.natAdd 21 l))
def extremal (i : Bit) := ([8,10,15,16,24,26,39,40] : List ℕ).contains i.val
def flip (i : Bit) : Input := fun j => decide (i=j) || extremal j
def holes := univ.filter fun i => extremal i = false

theorem extremal_zero : graph extremal = false := by decide +kernel
theorem holes_card : holes.card = 34 := by decide +kernel
theorem indispensable : ∀ i : Bit, extremal i = false → graph (flip i) = true := by decide +kernel

theorem lower (f : Expr) (correct : ∀ x, eval x f = graph x) : 6 ≤ depth f := by
  obtain ⟨S,n,z,k⟩ := certificate f extremal ((correct _).trans extremal_zero)
  have sub : holes ⊆ S := by
    intro i hi
    have off := (mem_filter.mp hi).2
    by_contra hn
    have h := k (flip i) (by intro j hj; have ne : i≠j := fun e => hn (e ▸ hj); simp [flip,ne,z j hj])
    rw [correct,indispensable i off] at h;cases h
  have c := (card_le_card sub).trans n
  rw [holes_card] at c
  by_contra! h
  have up : 2^depth f ≤ 2^5 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

def balanced : ℕ → (ℕ → Expr) → Expr
  | 0,f => f 0
  | d+1,f => .disj (balanced d f) (balanced d (fun i => f (2^d+i)))

theorem balanced_depth (d : ℕ) (f : ℕ → Expr) (zero : ∀ i, depth (f i)=0) :
    depth (balanced d f) = d := by
  induction d generalizing f with
  | zero => exact zero 0
  | succ d ih => simp [balanced,depth,ih _ zero,ih _ (fun i => zero (2^d+i))]

theorem balanced_true (d : ℕ) (f : ℕ → Expr) (x : Input) :
    eval x (balanced d f) = true ↔ ∃ i < 2^d, eval x (f i) = true := by
  induction d generalizing f with
  | zero => simp [balanced]
  | succ d ih =>
    simp only [balanced,eval,Bool.or_eq_true_iff,ih,pow_succ]
    constructor
    · rintro (⟨i,h,k⟩|⟨i,h,k⟩)
      · exact ⟨i,by omega,k⟩
      · exact ⟨2^d+i,by omega,k⟩
    · rintro ⟨i,h,k⟩
      by_cases lo : i<2^d
      · exact Or.inl ⟨i,lo,k⟩
      · exact Or.inr ⟨i-2^d,by omega,by simpa [Nat.add_sub_of_le (Nat.le_of_not_gt lo)] using k⟩

def clauseLeaf (S : Finset Bit) (i : ℕ) : Expr :=
  if hi : i<42 then (if (⟨i,hi⟩ : Bit) ∈ S then .var ⟨i,hi⟩ else .lit false) else .lit false
def clause (S : Finset Bit) := balanced 6 (clauseLeaf S)

theorem clause_depth (S) : depth (clause S)=6 :=
  balanced_depth _ _ (by intro i; unfold clauseLeaf;split <;> first | rfl | split <;> rfl)

theorem clause_true (S) (x : Input) : eval x (clause S) = true ↔ ∃ i∈S,x i=true := by
  rw [clause,balanced_true]
  constructor
  · rintro ⟨i,_,h⟩
    by_cases hi : i<42
    · by_cases hs : (⟨i,hi⟩ : Bit) ∈ S
      · exact ⟨⟨i,hi⟩,hs,by simpa [clauseLeaf,hi,hs,eval] using h⟩
      · simp [clauseLeaf,hi,hs,eval] at h
    · simp [clauseLeaf,hi,eval] at h
  · rintro ⟨i,hi,h⟩
    exact ⟨i.val,by have := i.isLt;norm_num;omega,by simpa [clauseLeaf,i.isLt,hi,eval] using h⟩

def cnf : List (Finset Bit) → Expr
  | [] => .lit true
  | S::ss => .conj (clause S) (cnf ss)

theorem cnf_depth (ss) : depth (cnf ss) ≤ 6 := by
  induction ss with | nil => decide | cons _ _ ih => simpa [cnf,depth,clause_depth] using ih

theorem cnf_true (ss) (x : Input) : eval x (cnf ss) = true ↔ ∀ S∈ss, ∃ i∈S,x i=true := by
  induction ss with
  | nil => simp [cnf,eval]
  | cons s ss ih => simp [cnf,eval,clause_true,ih]

def covers := (univ : Finset (Finset Bit)).filter fun S =>
  ∀ p l : Fin 21, adjacent p l → Fin.castAdd 21 p ∈ S ∨ Fin.natAdd 21 l ∈ S

theorem upper : ∃ f : Expr, depth f ≤ 6 ∧ ∀ x, eval x f = graph x := by
  classical
  refine ⟨cnf covers.toList,cnf_depth _,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [cnf_true,graph,decide_eq_true_eq]
  constructor
  · intro ok
    by_contra no
    let S := univ.filter fun i => x i = false
    have cover : S ∈ covers.toList := by
      simp only [covers,mem_toList,mem_filter,mem_univ,true_and]
      intro p l adj
      by_cases a : x (Fin.castAdd 21 p) = true
      · right; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; exact Bool.eq_false_iff.mpr (fun b => no ⟨p,l,adj,a,b⟩)
      · left; simp [S,Bool.eq_false_iff.mpr a]
    obtain ⟨i,hi,yes⟩ := ok S cover
    have off := (mem_filter.mp hi).2
    simp_all
  · rintro ⟨p,l,adj,a,b⟩ S hS
    have cv := (mem_filter.mp (mem_toList.mp hS)).2 p l adj
    exact cv.elim (fun h => ⟨_,h,a⟩) (fun h => ⟨_,h,b⟩)

end PEqualNP.Research.PlaneORDepth

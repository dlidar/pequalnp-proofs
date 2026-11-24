import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import PEqualNP.Defs

/-!
# The finite test family and rule simulation for L-meta-4055

The 105 incident pairs supply positive tests. A maximal negative pair is the
Galois closure of either side. If each side has at least six vertices, both
have exactly six. Thus seeds of size at most five on either side, plus
six-point seeds avoiding six lines, give every maximal negative.

Two external enumerations found 25,237 distinct maximal negatives, including
168 six-by-six pairs. One enumerated all point masks and tested closure. The
other deduplicated the canonical tests proved exhaustive below. These counts
are computational observations; the proofs do not assume them.

For the reduction, a disabled raw wire corresponds to its set of false test
positions. Conjunction takes an arbitrary union of these sets for free.
Each binary OR adjoins one intersection. The final theorem is the generic
simulation child on the two-child reduction branch.
-/

namespace PEqualNP.Research.PlaneFourTests
open Finset

def incident (p l : Fin 21) : Bool :=
  ([((p:ℕ)+20)%21, p.val, (p.val+5)%21, (p.val+7)%21, (p.val+17)%21] : List ℕ).contains l.val

def lines (p : Fin 21) := univ.filter fun l => incident p l
def points (l : Fin 21) := univ.filter fun p => incident p l

theorem plane_counts :
    (∀ p, (lines p).card = 5) ∧ (∀ l, (points l).card = 5) ∧
    (∀ p q, p ≠ q → (lines p ∩ lines q).card = 1) ∧
    (∀ l m, l ≠ m → (points l ∩ points m).card = 1) := by decide +kernel

-- Each new neighbourhood loses at most one element for each previously
-- selected vertex. The bound is sharp when no three share any neighbour.
theorem union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (N : α → Finset β) (degree : ∀ x, (N x).card = 5)
    (thin : ∀ x y, x ≠ y → (N x ∩ N y).card ≤ 1) (S : Finset α) :
    10*S.card ≤ 2*(S.biUnion N).card + S.card*(S.card-1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have sub : N x ∩ S.biUnion N ⊆ S.biUnion (fun y => N x ∩ N y) := by
      intro l h
      obtain ⟨hl,hS⟩ := mem_inter.mp h
      obtain ⟨y,hy,hn⟩ := mem_biUnion.mp hS
      exact mem_biUnion.mpr ⟨y,hy,mem_inter.mpr ⟨hl,hn⟩⟩
    have common : (N x ∩ S.biUnion N).card ≤ S.card := calc
      _ ≤ _ := card_le_card sub
      _ ≤ ∑ y ∈ S, (N x ∩ N y).card := card_biUnion_le
      _ ≤ ∑ _y ∈ S, 1 := sum_le_sum (fun y hy => thin x y (fun he => hx (he ▸ hy)))
      _ = _ := by simp
    rw [card_insert_of_notMem hx,biUnion_insert]
    have size := card_union_add_card_inter (N x) (S.biUnion N)
    rw [degree x] at size
    cases h : S.card with
    | zero => simp_all
    | succ k =>
      rw [h] at ih common
      simp only [Nat.succ_sub_one] at *
      nlinarith

def independent (P L : Finset (Fin 21)) : Prop :=
  ∀ p ∈ P, ∀ l ∈ L, incident p l = false

theorem six_rows {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
    (n : Fintype.card β = 21) (N : α → Finset β) (degree : ∀ x, (N x).card = 5)
    (thin : ∀ x y, x ≠ y → (N x ∩ N y).card ≤ 1) (P : Finset α) (L : Finset β)
    (avoid : ∀ p ∈ P, ∀ l ∈ L, l ∉ N p) (hP : 6 ≤ P.card) : L.card ≤ 6 := by
  classical
  obtain ⟨s,sub,sz⟩ := exists_subset_card_eq hP
  have count := union_bound N degree thin s
  rw [sz] at count
  have disj : Disjoint L (s.biUnion N) := by
    apply disjoint_left.mpr
    intro l hl joined
    obtain ⟨p,hp,hit⟩ := mem_biUnion.mp joined
    exact avoid p (sub hp) l hl hit
  have tot := card_le_univ (L ∪ s.biUnion N)
  rw [card_union_of_disjoint disj,n] at tot
  omega

theorem six_six {P L : Finset (Fin 21)} (h : independent P L) :
    P.card ≤ 5 ∨ L.card ≤ 5 ∨ (P.card = 6 ∧ L.card = 6) := by
  obtain ⟨dp,dl,tp,tl⟩ := plane_counts
  by_cases hp : 6 ≤ P.card
  · by_cases hl : 6 ≤ L.card
    · have one := six_rows (by simp) lines dp (fun i j ne => (tp i j ne).le) P L
          (fun p hp l hl => by simp [lines,h p hp l hl]) hp
      have two := six_rows (by simp) points dl (fun i j ne => (tl i j ne).le) L P
          (fun l hl p hp => by simp [points,h p hp l hl]) hl
      exact Or.inr (Or.inr ⟨by omega,by omega⟩)
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

def allowedLines (P : Finset (Fin 21)) : Finset (Fin 21) :=
  univ.filter fun l => ∀ p ∈ P, incident p l = false
def allowedPoints (L : Finset (Fin 21)) : Finset (Fin 21) :=
  univ.filter fun p => ∀ l ∈ L, incident p l = false

def maximal (P L : Finset (Fin 21)) : Prop :=
  independent P L ∧ ∀ A B, independent A B → P ⊆ A → L ⊆ B → A = P ∧ B = L

theorem closed_iff (P L : Finset (Fin 21)) :
    maximal P L ↔ P = allowedPoints L ∧ L = allowedLines P := by
  have left (P L) (h : independent P L) : P ⊆ allowedPoints L :=
    fun p hp => mem_filter.mpr ⟨mem_univ _,fun l hl => h p hp l hl⟩
  have right (P L) (h : independent P L) : L ⊆ allowedLines P :=
    fun l hl => mem_filter.mpr ⟨mem_univ _,fun p hp => h p hp l hl⟩
  have lr (L) : independent (allowedPoints L) L := fun _ h _ h' => (mem_filter.mp h).2 _ h'
  have rl (P) : independent P (allowedLines P) := fun _ h _ h' => (mem_filter.mp h').2 _ h
  constructor
  · rintro ⟨ind,m⟩
    exact ⟨(m _ _ (lr L) (left _ _ ind) Subset.rfl).1.symm,
      (m _ _ (rl P) Subset.rfl (right _ _ ind)).2.symm⟩
  · rintro ⟨hp,hl⟩
    refine ⟨by rw [hp]; exact lr L,?_⟩
    intro A B ind pa lb
    constructor
    · apply Subset.antisymm _ pa
      rw [hp]
      exact left A L (fun p h l h' => ind p h l (lb h'))
    · apply Subset.antisymm _ lb
      rw [hl]
      exact right P B (fun p h l h' => ind p (pa h) l h')

-- Starting from either side, fill the opposite side, then fill the
-- original side. Every resulting input is maximal, even for a seed
-- that was not closed.
theorem close_points (P : Finset (Fin 21)) :
    maximal (allowedPoints (allowedLines P)) (allowedLines P) := by
  rw [closed_iff]
  refine ⟨rfl,Subset.antisymm ?_ ?_⟩
  · intro l hl
    exact mem_filter.mpr ⟨mem_univ _,fun p hp => (mem_filter.mp hp).2 l hl⟩
  · intro l hl
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    intro p hp
    apply (mem_filter.mp hl).2 p
    exact mem_filter.mpr ⟨mem_univ _,fun k hk => (mem_filter.mp hk).2 p hp⟩

theorem close_lines (L : Finset (Fin 21)) :
    maximal (allowedPoints L) (allowedLines (allowedPoints L)) := by
  rw [closed_iff]
  refine ⟨Subset.antisymm ?_ ?_,rfl⟩
  · intro p hp
    exact mem_filter.mpr ⟨mem_univ _,fun l hl => (mem_filter.mp hl).2 p hp⟩
  · intro p hp
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    intro l hl
    apply (mem_filter.mp hp).2 l
    exact mem_filter.mpr ⟨mem_univ _,fun q hq => (mem_filter.mp hq).2 l hl⟩

def pointTest (P : Finset (Fin 21)) := (allowedPoints (allowedLines P), allowedLines P)
def lineTest (L : Finset (Fin 21)) := (allowedPoints L, allowedLines (allowedPoints L))

-- Exact equivalence for any proposed evaluator f, even without
-- monotonicity. In the last case the seed and its opposite both have
-- cardinality six.
theorem canonical_tests (f : Finset (Fin 21) → Finset (Fin 21) → Bool) :
    (∀ P L, maximal P L → f P L = false) ↔
      (∀ s, s.card ≤ 5 → f (pointTest s).1 (pointTest s).2 = false) ∧
      (∀ s, s.card ≤ 5 → f (lineTest s).1 (lineTest s).2 = false) ∧
      (∀ s, s.card = 6 → (allowedLines s).card = 6 → f (pointTest s).1 (pointTest s).2 = false) := by
  constructor
  · intro h
    exact ⟨fun s _ => h _ _ (close_points s),fun s _ => h _ _ (close_lines s),
      fun s _ _ => h _ _ (close_points s)⟩
  · rintro ⟨row,col,six⟩ P L h
    obtain ⟨hp,hl⟩ := (closed_iff _ _).mp h
    have rp : pointTest P = (P,L) := by simp [pointTest,←hl,←hp]
    have rl : lineTest L = (P,L) := by simp [lineTest,←hp,←hl]
    rcases six_six h.1 with p|l|⟨p,l⟩
    · simpa only [rp] using row P p
    · simpa only [rl] using col L l
    · simpa only [rp] using six P p (hl ▸ l)

theorem compile_signatures : ∀ (X : Type) (W : X → List Bool) (n : ℕ), (∀ x, (W x).length = n) →
    ∀ (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ),
    let close := fun (F : Set (Set X)) => {s : Set X | ∃ A ⊆ F, s = ⋃₀ A}
    let step := fun (F : Set (Set X)) (q : Set X × Set X) =>
      F ∪ {s | q.1 ∈ close F ∧ q.2 ∈ close F ∧ s = q.1 ∩ q.2}
    let pred := fun (V : X → List Bool) (i : ℕ) => {x | (V x).getD i false = false}
    let run := fun x => R.foldl (fun v r => v ++ [decide (∀ i ∈ r.1, v.getD i false = true) ||
                    decide (∀ i ∈ r.2, v.getD i false = true)]) (W x)
    ∃ Q : List (Set X × Set X), Q.length = R.length ∧
      {x | ∃ i ∈ out, (run x).getD i false = false} ∈ close (Q.foldl step (Set.range (pred W))) := by
  intro X W n len R out
  classical
  let close := fun (F : Set (Set X)) => {s : Set X | ∃ A ⊆ F, s = ⋃₀ A}
  let step := fun (F : Set (Set X)) (q : Set X × Set X) =>
    F ∪ {s | q.1 ∈ close F ∧ q.2 ∈ close F ∧ s = q.1 ∩ q.2}
  let pred := fun (V : X → List Bool) (i : ℕ) => {x | (V x).getD i false = false}
  let fail := fun (V : X → List Bool) (a : Finset ℕ) => {x | ∃ i ∈ a, (V x).getD i false = false}
  let update := fun (v : List Bool) (r : Finset ℕ × Finset ℕ) => v ++
    [decide (∀ i ∈ r.1, v.getD i false = true) || decide (∀ i ∈ r.2, v.getD i false = true)]
  have free (F : Set (Set X)) (V : X → List Bool) (available : ∀ i, pred V i ∈ F) (a : Finset ℕ) :
      fail V a ∈ close F := by
    refine ⟨pred V '' (a : Set ℕ),?_,?_⟩
    · rintro s ⟨i,_,rfl⟩; exact available i
    · ext x
      simp [fail,pred]
  have simulation (R : List (Finset ℕ × Finset ℕ)) (V : X → List Bool) (n : ℕ)
      (len : ∀ x, (V x).length = n) (F : Set (Set X)) (available : ∀ i, pred V i ∈ F) :
      ∃ Q : List (Set X × Set X), Q.length = R.length ∧
        ∀ i, pred (fun x => R.foldl update (V x)) i ∈ Q.foldl step F := by
    induction R generalizing V n F with
    | nil => exact ⟨[],rfl,available⟩
    | cons r tail ih =>
      let U := fun x => update (V x) r
      let q := (fail V r.1, fail V r.2)
      have newlen (x) : (U x).length = n+1 := by simp [U,update,len]
      have next (i) : pred U i ∈ step F q := by
        by_cases eq : i = n
        · subst i
          apply Or.inr
          refine ⟨free _ _ available _,free _ _ available _,?_⟩
          ext x
          simp [pred,U,update,List.getD_eq_getElem?_getD,len,fail,q]
        · apply Or.inl
          have same : pred U i = pred V i := by
            ext x
            by_cases hi : i < n
            · simp [pred,U,update,List.getD_eq_getElem?_getD,List.getElem?_append,len,hi]
            · have large : (U x).length ≤ i := by rw [newlen]; omega
              have old : (V x).length ≤ i := by rw [len]; omega
              simp [pred,List.getD_eq_getElem?_getD,List.getElem?_eq_none large,List.getElem?_eq_none old]
          simpa only [same] using available i
      obtain ⟨Q,sz,rep⟩ := ih U (n+1) newlen (step F q) next
      exact ⟨q::Q,by simp [sz],rep⟩
  obtain ⟨Q,sz,available⟩ := simulation R W n len (Set.range (pred W)) (fun i => ⟨i,rfl⟩)
  exact ⟨Q,sz,free _ _ available out⟩

end PEqualNP.Research.PlaneFourTests

import Mathlib.Tactic

/-! A pair of paths of length 2k, with disjoint rungs joining equal even
positions. A pattern stores the selected vertices, from left to right.
"residual" checks both paths and "rungs" checks the deleted edges. -/
namespace PEqualNP.Research.RungCovers

inductive Pattern where
  | tip (top bottom : Bool)
  | step (top bottom topOdd bottomOdd : Bool) (tail : Pattern)
  deriving DecidableEq

namespace Pattern
def len : Pattern → Nat
  | .tip .. => 0
  | .step _ _ _ _ t => t.len + 1
def weight : Pattern → Nat
  | .tip a b => a.toNat + b.toNat
  | .step a b x y t => a.toNat + b.toNat + x.toNat + y.toNat + t.weight
def top : Pattern → Bool
  | .tip a _ | .step a _ _ _ _ => a
def bottom : Pattern → Bool
  | .tip _ b | .step _ b _ _ _ => b

def residual : Pattern → Prop
  | .tip _ _ => True
  | .step a b x y t =>
    (a || x) = true ∧ (x || t.top) = true ∧
    (b || y) = true ∧ (y || t.bottom) = true ∧ t.residual
def rungs : Pattern → Prop
  | .tip a b => (a || b) = true
  | .step a b _ _ t => (a || b) = true ∧ t.rungs
def allOdds : Pattern → Prop
  | .tip _ _ => True
  | .step _ _ x y t => x = true ∧ y = true ∧ t.allOdds
def onlyOdds : Pattern → Prop
  | .tip a b => a = false ∧ b = false
  | .step a b x y t => a = false ∧ b = false ∧ x = true ∧ y = true ∧ t.onlyOdds

theorem onlyOdds_head (r : Pattern) (h : r.onlyOdds) :
    r.top = false ∧ r.bottom = false := by
  cases r <;> simp_all [onlyOdds,top,bottom]

theorem residual_optimum (r : Pattern) (h : r.residual) :
    2 * r.len ≤ r.weight ∧ (r.weight = 2 * r.len → r.onlyOdds) := by
  induction r with
  | tip a b => cases a <;> cases b <;> simp [len,weight,onlyOdds]
  | step a b x y t ih =>
    obtain ⟨l, lx, m, my, tail⟩ := h
    obtain ⟨low,tight⟩ := ih tail
    have shrink : t.weight = 2 * t.len → t.top = false ∧ t.bottom = false :=
      fun eq => onlyOdds_head t (tight eq)
    by_cases eq : t.weight = 2 * t.len
    · have heads := shrink eq
      have tailForm := tight eq
      cases a <;> cases b <;> cases x <;> cases y <;>
        simp_all [len, weight, onlyOdds, Nat.mul_add] <;> omega
    · cases a <;> cases b <;> cases x <;> cases y <;>
        simp_all [len, weight, onlyOdds, Nat.mul_add] <;> omega

theorem full_lower (r : Pattern) (h : r.residual) (f : r.rungs) :
    2 * r.len + 1 ≤ r.weight := by
  obtain ⟨low,tight⟩ := residual_optimum r h
  by_contra! fail
  have e : r.weight = 2 * r.len := by omega
  have hh := onlyOdds_head r (tight e)
  cases r <;> simp_all [top,bottom,rungs]

theorem extending_lower (r : Pattern) (f : r.rungs) (a : r.allOdds) :
    3 * r.len + 1 ≤ r.weight := by
  induction r with
  | tip a b => cases a <;> cases b <;> simp_all [rungs,len,weight]
  | step a b x y t ih =>
    obtain ⟨hit,tail⟩ := f
    obtain ⟨rfl,rfl,keep⟩ := a
    have low := ih tail keep
    cases a <;> cases b <;> simp_all [len,weight, Nat.mul_add] <;> omega

def uniform (a b x y : Bool) : Nat → Pattern
  | 0 => .tip a b
  | k+1 => .step a b x y (uniform a b x y k)

theorem uniform_head (a b x y : Bool) (k : Nat) :
    (uniform a b x y k).top = a ∧ (uniform a b x y k).bottom = b := by
  cases k <;> exact ⟨rfl,rfl⟩

theorem uniform_len (a b x y : Bool) (k : Nat) : (uniform a b x y k).len = k := by
  induction k <;> simp_all [uniform,len]

theorem sharp_examples (k : Nat) :
    let h := uniform false false true true k
    let g := uniform true false false true k
    let e := uniform true false true true k
    (h.residual ∧ h.onlyOdds ∧ h.weight = 2*k) ∧
    (g.residual ∧ g.rungs ∧ g.weight = 2*k+1) ∧
    (e.residual ∧ e.rungs ∧ e.allOdds ∧ e.weight = 3*k+1) := by
  induction k with
  | zero => simp [uniform, residual, onlyOdds, weight, rungs, allOdds]
  | succ k ih =>
    have heads := uniform_head true false false true k
    dsimp only at ih ⊢
    simp_all [uniform, residual, onlyOdds, weight, rungs, allOdds, Nat.mul_add] <;> omega

end Pattern
end PEqualNP.Research.RungCovers

namespace PEqualNP.Research.RungCovers
abbrev Point := Bool × Nat

/-- The two finite paths have coordinates 0 through 2k. -/
def rail (p q : Point) : Prop :=
  p.1 = q.1 ∧ (p.2+1 = q.2 ∨ q.2+1 = p.2)
def rung (p q : Point) : Prop :=
  p.1 ≠ q.1 ∧ p.2 = q.2 ∧ p.2 % 2 = 0
def edge (k : Nat) (p q : Point) : Prop :=
  p.2 ≤ 2*k ∧ q.2 ≤ 2*k ∧ (rail p q ∨ rung p q)

theorem symmetric_edge (k : Nat) {p q : Point} (h : edge k p q) : edge k q p := by
  rcases h with ⟨hp,hq,h | h⟩
  · exact ⟨hq,hp,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
  · exact ⟨hq,hp,Or.inr ⟨Ne.symm h.1,h.2.1.symm,h.2.1 ▸ h.2.2⟩⟩

def color (p : Point) : Bool := xor p.1 (p.2 % 2 == 1)

theorem bipartite_edge {k : Nat} {p q : Point} (h : edge k p q) : color p ≠ color q := by
  obtain ⟨a,i⟩ := p
  obtain ⟨b,j⟩ := q
  rcases h with ⟨_,_,h | h⟩ <;> cases a <;> cases b <;>
    simp_all [color,rail,rung] <;> omega

/-- Two distinct vertices have at most one common neighbor, for every k. -/
theorem unique_common_neighbor {k : Nat} {p q u v : Point}
    (h : p ≠ q) (hu : edge k p u) (iu : edge k q u)
    (hv : edge k p v) (iv : edge k q v) : u = v := by
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  rcases u with ⟨c,s⟩
  rcases v with ⟨d,t⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [edge, rail, rung, Prod.mk.injEq] <;> omega

namespace Pattern
/-- Turn an arbitrary choice of vertices into a pattern. The Boolean row
label true denotes the top row. -/
def encode (k : Nat) (f : Bool → Nat → Bool) : Pattern :=
  match k with
  | 0 => .tip (f true 0) (f false 0)
  | k+1 => .step (f true 0) (f false 0) (f true 1) (f false 1)
      (encode k (fun row i => f row (i+2)))

theorem encode_head (k : Nat) (f : Bool → Nat → Bool) :
    (encode k f).top = f true 0 ∧ (encode k f).bottom = f false 0 := by
  cases k <;> exact ⟨rfl,rfl⟩

theorem encode_len (k : Nat) (f : Bool → Nat → Bool) : (encode k f).len = k := by
  induction k generalizing f <;> simp_all [encode,len]

/-- Independent specification of all edges on one of the paths. -/
def railsCovered (k : Nat) (f : Bool → Nat → Bool) : Prop :=
  ∀ row i, i < 2*k → (f row i || f row (i+1)) = true
def rungsCovered (k : Nat) (f : Bool → Nat → Bool) : Prop :=
  ∀ i ≤ k, (f true (2*i) || f false (2*i)) = true

theorem encode_residual (k : Nat) (f : Bool → Nat → Bool) :
    (encode k f).residual ↔ railsCovered k f := by
  induction k generalizing f with
  | zero => simp [encode,residual,railsCovered]
  | succ k ih =>
    let tail := fun row i => f row (i+2)
    have hd := encode_head k tail
    change ((_ ∧ _ ∧ _ ∧ _ ∧ (encode k tail).residual) ↔ _)
    rw [hd.1, hd.2, ih]
    dsimp only [tail, Nat.zero_add]
    constructor
    · rintro ⟨a,b,c,d,e⟩ row i hi
      cases i with
      | zero => cases row <;> assumption
      | succ i =>
        cases i with
        | zero => cases row <;> assumption
        | succ i => exact e row i (by omega)
    · intro ok
      refine ⟨ok true 0 (by omega), ok true 1 (by omega), ok false 0 (by omega),
        ok false 1 (by omega), ?_⟩
      intro row i hi
      exact ok row (i+2) (by omega)

theorem encode_rungs (k : Nat) (f : Bool → Nat → Bool) :
    (encode k f).rungs ↔ rungsCovered k f := by
  induction k generalizing f with
  | zero => simp [encode,rungs,rungsCovered]
  | succ k ih =>
    change (_ ∧ (encode k _).rungs ↔ _)
    rw [ih]
    constructor
    · rintro ⟨a,tail⟩ i hi
      cases i with
      | zero => exact a
      | succ i => simpa [Nat.mul_succ] using tail i (by omega)
    · intro ok
      refine ⟨ok 0 (by omega), ?_⟩
      intro i hi
      simpa [Nat.mul_succ] using ok (i+1) (by omega)

theorem encode_weight (k : Nat) (f : Bool → Nat → Bool) :
    (encode k f).weight =
      ∑ i ∈ Finset.range (2*k+1), ((f true i).toNat + (f false i).toNat) := by
  induction k generalizing f with
  | zero => simp [encode,weight]
  | succ k ih =>
    simp only [encode,weight,ih]
    conv_rhs =>
      rw [show 2*(k+1)+1 = ((2*k+1)+1)+1 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega

theorem edge_cover_iff (k : Nat) (f : Bool → Nat → Bool) :
    (∀ p q, edge k p q → (f p.1 p.2 || f q.1 q.2) = true) ↔
      (encode k f).residual ∧ (encode k f).rungs := by
  rw [encode_residual, encode_rungs]
  constructor
  · intro h
    constructor
    · intro row i hi
      exact h (row,i) (row,i+1) ⟨by dsimp; omega, by dsimp; omega, Or.inl ⟨rfl,Or.inl rfl⟩⟩
    · intro i hi
      exact h (true,2*i) (false,2*i) ⟨by dsimp; omega,by dsimp; omega,
        Or.inr ⟨by simp,rfl,by dsimp; omega⟩⟩
  · rintro ⟨a,b⟩ ⟨r,i⟩ ⟨s,j⟩ ⟨hi,hj,h | h⟩
    · rcases h with ⟨rfl,h | h⟩
      · change i+1 = j at h
        subst j
        exact a _ _ (by dsimp at hj; omega)
      · change j+1 = i at h
        subst i
        rw [Bool.or_comm]
        exact a _ _ (by dsimp at hi; omega)
    · rcases h with ⟨rs,h,even⟩
      change i = j at h
      subst j
      change i % 2 = 0 at even
      have e : 2*(i/2) = i := by omega
      have w := b (i/2) (by dsimp at hi; omega)
      rw [e] at w
      cases r <;> cases s <;> simp_all [Bool.or_comm]

end Pattern
end PEqualNP.Research.RungCovers

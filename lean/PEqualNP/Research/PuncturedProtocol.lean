import PEqualNP.Research.PuncturedPositiveCost

namespace PEqualNP.Research.PuncturedPlaneCut
open Finset

/-- Each query is local to the player named at that node. At a leaf both players know the answer. -/
inductive Protocol
  | leaf (out : Bool)
  | point (q : Side → Bool) (yes no : Protocol)
  | line (q : Side → Bool) (yes no : Protocol)

def Protocol.eval : Protocol → Side → Side → Bool
  | .leaf b,_,_ => b
  | .point q p r,x,y => if q x then p.eval x y else r.eval x y
  | .line q p r,x,y => if q y then p.eval x y else r.eval x y

def Protocol.leaves (b : Bool) : Protocol → Nat
  | .leaf a => if a=b then 1 else 0
  | .point _ p r | .line _ p r => p.leaves b + r.leaves b

def Protocol.depth : Protocol → Nat
  | .leaf _ => 0
  | .point _ p r | .line _ p r => max p.depth r.depth + 1

def Factors (K : Type*) [Field K] (k : Nat) (f : Side → Side → K) :=
  ∃ A B : Fin k → Side → K, ∀ x y, f x y = ∑ i, A i x * B i y

theorem join_factors {K : Type*} [Field K] {k m} {f g : Side → Side → K} (F : Factors K k f) (G : Factors K m g)
    (q : Side → Bool) :
    Factors K (k+m) (fun x y => if q x then f x y else g x y) ∧
    Factors K (k+m) (fun x y => if q y then f x y else g x y) := by
  obtain ⟨A,B,h⟩ := F
  obtain ⟨C,D,t⟩ := G
  constructor
  · refine ⟨Fin.addCases (fun i x => if q x then A i x else 0) (fun j x => if q x then 0 else C j x),
      Fin.addCases B D,?_⟩
    intro x y
    rw [Fin.sum_univ_add]
    cases e : q x <;> simp [e,h,t]
  · refine ⟨Fin.addCases A C,
      Fin.addCases (fun i y => if q y then B i y else 0) (fun j y => if q y then 0 else D j y),?_⟩
    intro x y
    rw [Fin.sum_univ_add]
    cases e : q y <;> simp [e,h,t]

theorem Protocol.factors (p : Protocol) (K : Type*) [Field K] (b : Bool) :
    Factors K (p.leaves b) (fun x y => if p.eval x y = b then 1 else 0) := by
  induction p with
  | leaf a =>
    by_cases h : a=b
    · simp only [Protocol.leaves,h,ite_true]
      exact ⟨fun _ _ => 1,fun _ _ => 1,by simp [Protocol.eval,h]⟩
    · simp only [Protocol.leaves,h,ite_false]
      exact ⟨fun _ _ => 0,fun _ _ => 0,by simp [Protocol.eval,h]⟩
  | point q p r ih jh =>
    convert (join_factors ih jh q).1 using 2 <;> first | rfl | skip
    rename_i x
    funext y
    cases e : q x <;> simp [Protocol.eval,e]
  | line q p r ih jh =>
    convert (join_factors ih jh q).2 using 2 <;> first | rfl | skip
    rename_i x
    funext y
    cases e : q y <;> simp [Protocol.eval,e]

theorem Protocol.capacity (p : Protocol) : p.leaves false + p.leaves true ≤ 2^p.depth := by
  induction p with
  | leaf a => cases a <;> decide
  | point q p r ih jh | line q p r ih jh =>
    simp only [Protocol.leaves,Protocol.depth,pow_succ]
    have a := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_max_left p.depth r.depth)
    have b := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_max_right p.depth r.depth)
    omega

theorem public_output_bounds (p : Protocol)
    (exactOn : ∀ x y, p.eval x y = posted (input 21 [] x y)) :
    24925 ≤ p.leaves false ∧ 24924 ≤ p.leaves true ∧ 16 ≤ p.depth := by
  obtain ⟨A,B,h⟩ := p.factors ℚ false
  have lo := separated_products_lower ℚ A B (by
    intro x y; rw [← h]; simp only [exactOn]; cases v : posted (input 21 [] x y) <;> simp [zeroRow,v])
  obtain ⟨C,D,t⟩ := p.factors ℚ true
  have hi := positive_products_lower ℚ C D (by
    intro x y; rw [← t]; simp only [exactOn]; cases v : posted (input 21 [] x y) <;> simp [oneRow,v])
  refine ⟨lo,hi,?_⟩
  by_contra! small
  have cap := p.capacity
  have bound := Nat.pow_le_pow_right (by decide : 0<2) (show p.depth ≤ 15 by omega)
  omega

def readBits {k : Nat} (enc : Side → Fin k → Bool) (dec : (Fin k → Bool) → Side → Bool) : Protocol :=
  match k with
  | 0 => .line (dec fun i => Fin.elim0 i) (.leaf true) (.leaf false)
  | k+1 => .point (fun x => enc x 0)
    (readBits (fun x i => enc x i.succ) (fun t => dec (Fin.cons true t)))
    (readBits (fun x i => enc x i.succ) (fun t => dec (Fin.cons false t)))

theorem readBits_ok {k : Nat} (enc : Side → Fin k → Bool) (dec : (Fin k → Bool) → Side → Bool) :
    (∀ x y, (readBits enc dec).eval x y = dec (enc x) y) ∧ (readBits enc dec).depth = k+1 := by
  induction k with
  | zero =>
    have eq (x : Side) : (fun i : Fin 0 => Fin.elim0 (α:=Bool) i) = enc x := funext fun i => i.elim0
    constructor
    · intro x y; simp [readBits,Protocol.eval,eq x]
    · rfl
  | succ k ih =>
    have pos := ih (fun x i => enc x i.succ) (fun t => dec (Fin.cons true t))
    have neg := ih (fun x i => enc x i.succ) (fun t => dec (Fin.cons false t))
    constructor
    · intro x y
      simp only [readBits,Protocol.eval]
      cases h : enc x 0
      · simp only [Bool.false_eq_true,ite_false,neg.1]
        rw [←h]
        exact congrArg (fun v => dec v y) (Fin.cons_self_tail (q:=enc x))
      · simp only [ite_true,pos.1]
        rw [←h]
        exact congrArg (fun v => dec v y) (Fin.cons_self_tail (q:=enc x))
    · simp [readBits,Protocol.depth,pos.2,neg.2]

theorem public_output_attained : ∃ p : Protocol, p.depth = 16 ∧
    ∀ x y, p.eval x y = posted (input 21 [] x y) := by
  obtain ⟨enc,dec,good⟩ := (binary_width (b:=15) (by decide : 21≤21) [] (by simp)).mpr
    (by rw [full_count]; decide)
  exact ⟨readBits enc dec,(readBits_ok enc dec).2,fun x y => ((readBits_ok enc dec).1 x y).trans (good x y).symm⟩

end PEqualNP.Research.PuncturedPlaneCut

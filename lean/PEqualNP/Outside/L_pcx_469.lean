import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_469


namespace SpinMass
open Finset
abbrev T (t : ℕ) := Fin t
abbrev V (t : ℕ) := Option (Fin t × Bool)
abbrev Pair (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}
abbrev E (t : ℕ) := Fin 3 × Fin t
abbrev Mask (t : ℕ) := Fin t → Fin 3
def tail {t : ℕ} (e : E t) : V t := if e.1 = 0 then some (e.2,false) else none
def head {t : ℕ} (e : E t) : V t := some (e.2,decide (e.1 ≠ 1))
def active {t : ℕ} (g : Option (Pair t)) (i : Fin t) : Bool :=
  g.elim false (fun p => decide (p.val.1 = i ∨ p.val.2 = i))
def weight {t : ℕ} (g : Option (Pair t)) (e : E t) (diff : Bool) : ℕ :=
  if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
  if active g e.2 then (if diff then 1 else 3) else 2
def obs {t : ℕ} (g : Option (Pair t)) (p : Mask t) : ℕ :=
  ∑ x : V t → Bool, if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
    (Finset.univ.filter (fun e : E t => x (tail e) ≠ x (head e))).card = 2*t then
    ∏ e : E t, weight g e (xor (x (tail e)) (x (head e))) else 0

def spinEquiv (t : ℕ) : (V t → Bool) ≃ Bool × (Fin t → Bool × Bool) where
  toFun x := (x none, fun i => (x (some (i,false)),x (some (i,true))))
  invFun u
    | none => u.1
    | some (i,false) => (u.2 i).1
    | some (i,true) => (u.2 i).2
  left_inv x := by funext a; cases a with
                   | none => rfl
                   | some z => rcases z with ⟨i,b⟩; cases b <;> rfl
  right_inv u := by rcases u with ⟨c,u⟩; rfl

def localWeight (c : Bool) (a : Bool) (z : Fin 3) (u : Bool × Bool) : ℕ :=
  if (z = 0 ∨ z = (if u.1 then 2 else 1)) ∧ u.1 ≠ u.2 then
    if a then (if xor c u.1 then 1 else 3) else 2
  else 0

theorem cut_count {t : ℕ} (x : V t → Bool)
    (h : ∀ i, x (some (i,false)) ≠ x (some (i,true))) :
    (Finset.univ.filter (fun e : E t => x (tail e) ≠ x (head e))).card = 2*t := by
  classical
  have hh := Finset.sum_boole (R := ℕ) (fun e : E t => x (tail e) ≠ x (head e)) Finset.univ
  rw [Nat.cast_id] at hh
  rw [← hh]
  rw [Fintype.sum_prod_type_right]
  have at_i (i : Fin t) : (∑ j : Fin 3, if x (tail (j,i)) ≠ x (head (j,i)) then 1 else 0 : ℕ) = 2 := by
    have hi := h i
    rw [Fin.sum_univ_three]
    simp [tail, head]
    cases hc : x none <;> cases ha : x (some (i,false)) <;> cases hb : x (some (i,true)) <;> simp_all
  simp only [at_i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change t * 2 = 2 * t
  omega

theorem term_factor {t : ℕ} (g : Option (Pair t)) (p : Mask t) (x : V t → Bool) :
    (if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : E t => x (tail e) ≠ x (head e))).card = 2*t then
      ∏ e : E t, weight g e (xor (x (tail e)) (x (head e))) else 0) =
    ∏ i, localWeight (x none) (active g i) (p i) ((spinEquiv t x).2 i) := by
  classical
  let good := fun i : Fin t => p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)
  let opp := fun i : Fin t => x (some (i,false)) ≠ x (some (i,true))
  have prod_raw : (∏ e : E t, weight g e (xor (x (tail e)) (x (head e)))) =
      ∏ i, ((xor (x (some (i,false))) (x (some (i,true)))).toNat *
             (if active g i then (if xor (x none) (x (some (i,false))) then 1 else 3) else 2)) := by
    rw [Fintype.prod_prod_type_right]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fin.prod_univ_three]
    simp [weight, tail, head]
  rw [prod_raw]
  by_cases ho : ∀ i, opp i
  · have hc := cut_count x ho
    by_cases hg : ∀ i, good i
    · rw [if_pos ⟨hg,hc⟩]
      apply Finset.prod_congr rfl
      intro i _
      have hi := ho i
      have hm := hg i
      simp only [opp] at hi
      simp only [good] at hm
      have hx : ∀ a b : Bool, a ≠ b → (xor a b).toNat = 1 := by decide
      change _ = (if (p i = 0 ∨ p i = _) ∧ x (some (i,false)) ≠ x (some (i,true)) then _ else 0)
      simp only [hx _ _ hi, one_mul]
      exact (if_pos (show good i ∧ opp i from ⟨hm,hi⟩)).symm
    · obtain ⟨i,hi⟩ := Classical.not_forall.mp hg
      rw [if_neg (fun h => hg h.1)]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change (if good i ∧ opp i then _ else 0) = 0
      rw [if_neg (fun hh => hi hh.1)]
  · obtain ⟨i,hi⟩ := Classical.not_forall.mp ho
    have he : x (some (i,false)) = x (some (i,true)) := Classical.not_not.mp hi
    have lhs : (∏ j : Fin t, ((xor (x (some (j,false))) (x (some (j,true)))).toNat *
             (if active g j then (if xor (x none) (x (some (j,false))) then 1 else 3) else 2))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [he]
    rw [lhs,ite_self]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [localWeight, spinEquiv, he]

def site (c a : Bool) (z : Fin 3) : ℕ :=
  ∑ u : Bool × Bool, localWeight c a z u

theorem obs_product {t : ℕ} (g : Option (Pair t)) (p : Mask t) :
    obs g p = ∑ c : Bool, ∏ i, site c (active g i) (p i) := by
  classical
  unfold obs
  simp_rw [term_factor]
  let F := fun u : Bool × (Fin t → Bool × Bool) =>
    ∏ i, localWeight u.1 (active g i) (p i) (u.2 i)
  change (∑ x, F (spinEquiv t x)) = _
  rw [(spinEquiv t).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  exact (Fintype.prod_sum (fun i u => localWeight c (active g i) (p i) u)).symm

def raw (z : Fin 3) : ℕ := if z = 0 then 4 else 2
def factor (z w : Fin 3) : ℕ := if z = 0 ∨ w = 0 then 4 else if z = w then 5 else 3
theorem inactive : ∀ c z, site c false z = raw z := by decide
theorem pair_table : ∀ z w, 4 * (site true true z * site true true w +
      site false true z * site false true w) = 2 * raw z * raw w * factor z w := by decide

theorem two_sites {t : ℕ} (f : Fin t → ℕ) (i j : Fin t) (h : i ≠ j) :
    (∏ n, f n) = ((univ.erase i).erase j).prod f * f j * f i := by
  rw [Finset.prod_erase_mul _ _ (by simp [h.symm] : j ∈ univ.erase i),
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

def tag {t : ℕ} (g : Option (Pair t)) (p : Mask t) : ℕ :=
  g.elim 4 (fun e => factor (p e.val.1) (p e.val.2))

theorem mass_identity {t : ℕ} (g : Option (Pair t)) (p : Mask t) :
    4 * obs g p = 2 * (∏ i, raw (p i)) * tag g p := by
  rw [obs_product, Fintype.sum_bool]
  cases g with
  | none =>
    simp only [active, Option.elim, inactive, tag]
    ring
  | some e =>
    let i := e.val.1
    let j := e.val.2
    have hij : i ≠ j := ne_of_lt e.property
    let R := ((univ.erase i).erase j).prod (fun n => raw (p n))
    have he (c : Bool) : (∏ n, site c (active (some e) n) (p n)) =
        R * site c true (p j) * site c true (p i) := by
      rw [two_sites _ i j hij]
      have hrest : ((univ.erase i).erase j).prod (fun n => site c (active (some e) n) (p n)) = R := by
        apply Finset.prod_congr rfl
        intro n hn
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hn
        have hni : e.val.1 ≠ n := Ne.symm hn.2
        have hnj : e.val.2 ≠ n := Ne.symm hn.1
        simp [active, hni, hnj, inactive]
      rw [hrest]
      simp [active, i, j]
    rw [he true, he false, two_sites (fun n => raw (p n)) i j hij]
    change 4 * (R * _ * _ + R * _ * _) = 2 * (R * _ * _) * factor (p i) (p j)
    linear_combination R * pair_table (p i) (p j)

end SpinMass

namespace SpinMass
open Finset
theorem raw_pos : ∀ z, 0 < raw z := by decide
theorem raw_le : ∀ z, raw z ≤ 4 := by decide
theorem factor_pos : ∀ z w, 0 < factor z w := by decide
theorem factor_le : ∀ z w, factor z w ≤ 5 := by decide
theorem tag_pos {t : ℕ} (g : Option (Pair t)) (p : Mask t) : 0 < tag g p := by
  cases g with
  | none => exact (by decide : 0 < 4)
  | some e => exact factor_pos _ _
theorem tag_le {t : ℕ} (g : Option (Pair t)) (p : Mask t) : tag g p ≤ 5 := by
  cases g with
  | none => exact (by decide : 4 ≤ 5)
  | some e => exact factor_le _ _
theorem rawprod_pos {t : ℕ} (p : Mask t) : 0 < ∏ i, raw (p i) :=
  Finset.prod_pos (fun i _ => raw_pos _)
theorem obs_pos {t : ℕ} (g : Option (Pair t)) (p : Mask t) : 0 < obs g p := by
  have := mass_identity g p
  have h := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (rawprod_pos p)) (tag_pos g p)
  omega
theorem obs_le {t : ℕ} (g : Option (Pair t)) (p : Mask t) : obs g p ≤ 2^(2*t+2) := by
  have h₁ : (∏ i, raw (p i)) ≤ 4^t := by
    simpa using (Finset.prod_le_prod' (s := (univ : Finset (Fin t))) (g := fun _ => 4) (fun i _ => raw_le (p i)))
  have h₂ := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h₁) (tag_le g p)
  rw [← mass_identity] at h₂
  rw [pow_add, pow_mul]
  norm_num at *
  omega
def reading {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) := ∏ l, obs (G l) p
theorem reading_bound {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) :
    reading G p < 2^(k*(2*t+2)+1) := by
  have h : reading G p ≤ (2^(2*t+2))^k := by
    simpa [reading] using (Finset.prod_le_prod' (s := (univ : Finset (Fin k))) (g := fun _ => 2^(2*t+2)) (fun l _ => obs_le (G l) p))
  rw [← pow_mul,Nat.mul_comm] at h
  rw [pow_succ]
  have : 0 < 2^(k*(2*t+2)) := by positivity
  omega

theorem val_raw {q : ℕ} (hq : q = 3 ∨ q = 5) (z : Fin 3) : (raw z).factorization q = 0 := by
  rcases hq with rfl | rfl <;> fin_cases z <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide

theorem val_tag {t q : ℕ} (hq : q = 3 ∨ q = 5) (g : Option (Pair t)) (p : Mask t) :
    (tag g p).factorization q = if tag g p = q then 1 else 0 := by
  have aux : ∀ q z w, (q = 3 ∨ q = 5) → (factor z w).factorization q = if factor z w = q then 1 else 0 := by
    intro q z w h; rcases h with rfl | rfl <;> fin_cases z <;> fin_cases w <;> first | exact Nat.Prime.factorization_self (by decide : Nat.Prime 3) | exact Nat.Prime.factorization_self (by decide : Nat.Prime 5) | exact Nat.factorization_eq_zero_of_not_dvd (by decide)
  cases g with
  | none => rcases hq with rfl | rfl <;> exact Nat.factorization_eq_zero_of_not_dvd (n := 4) (by decide)
  | some e => exact aux q _ _ hq

theorem val_obs {t q : ℕ} (hq : q = 3 ∨ q = 5) (g : Option (Pair t)) (p : Mask t) :
    (obs g p).factorization q = if tag g p = q then 1 else 0 := by
  have h := congrArg (fun n : ℕ => n.factorization q) (mass_identity g p)
  have h2 : (2:ℕ).factorization q = 0 := by rcases hq with rfl | rfl <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide
  have h4 : (4:ℕ).factorization q = 0 := by rcases hq with rfl | rfl <;> apply Nat.factorization_eq_zero_of_not_dvd <;> decide
  simp only [Nat.factorization_mul (by decide : 4 ≠ 0) (obs_pos g p).ne',
    Nat.factorization_mul (Nat.mul_ne_zero (by decide : 2 ≠ 0) (rawprod_pos p).ne') (tag_pos g p).ne',
    Nat.factorization_mul (by decide : 2 ≠ 0) (rawprod_pos p).ne',
    Nat.factorization_prod (fun i _ => (raw_pos (p i)).ne'),
    Finsupp.add_apply, Finsupp.finsetSum_apply, val_raw hq, Finset.sum_const_zero,
    h2,h4,zero_add, val_tag hq] at h
  exact h

theorem val_reading {t k q : ℕ} (hq : q = 3 ∨ q = 5)
    (G : Fin k → Option (Pair t)) (p : Mask t) :
    (reading G p).factorization q = (univ.filter (fun l => tag (G l) p = q)).card := by
  unfold reading
  rw [Nat.factorization_prod (fun l _ => (obs_pos (G l) p).ne'), Finsupp.finsetSum_apply]
  simp_rw [val_obs hq]
  exact Finset.sum_boole _ _

def sign (z : Fin 3) : ℤ := if z = 0 then 0 else if z = 1 then -1 else 1
def edgeSign {t : ℕ} (g : Option (Pair t)) (p : Mask t) : ℤ :=
  g.elim 0 (fun e => sign (p e.val.1) * sign (p e.val.2))
theorem sign_table {t : ℕ} (g : Option (Pair t)) (p : Mask t) :
    edgeSign g p = (if tag g p = 5 then 1 else 0) - (if tag g p = 3 then 1 else 0) := by
  cases g with
  | none => rfl
  | some e =>
    exact (by decide : ∀ z w, sign z * sign w = (if factor z w = 5 then 1 else 0) - (if factor z w = 3 then 1 else 0)) _ _
theorem signed_reading {t k : ℕ} (G : Fin k → Option (Pair t)) (p : Mask t) :
    (∑ l, edgeSign (G l) p) = ((reading G p).factorization 5 : ℤ) - ((reading G p).factorization 3 : ℤ) := by
  simp_rw [sign_table, Finset.sum_sub_distrib]
  rw [val_reading (Or.inr rfl),val_reading (Or.inl rfl),Finset.sum_boole,Finset.sum_boole]
end SpinMass


namespace TernaryGrid
open Finset

def val (x : Fin 3) : ℤ := if x = 0 then 0 else if x = 1 then -1 else 1
def nz (x : ℤ) : ℕ := if x = 0 then 0 else 1
theorem affine_support (a b : ℤ) :
    2 * nz a ≤ ∑ x : Fin 3, nz (a * val x + b) := by
  rw [Fin.sum_univ_three]
  change 2 * nz a ≤ nz (a*0+b) + nz (a*(-1)+b) + nz (a*1+b)
  simp only [mul_zero,zero_add,mul_neg,mul_one]
  unfold nz
  split_ifs <;> omega

theorem square_support (c a b e : ℤ) :
    4 * nz c ≤ ∑ x : Fin 3, ∑ y : Fin 3,
      nz (c * val x * val y + a * val x + b * val y + e) := by
  have h := affine_support c b
  have hh (x : Fin 3) : 2 * nz (c*val x+b) ≤ ∑ y : Fin 3,
      nz (c * val x * val y + a * val x + b * val y + e) := by
    convert affine_support (c*val x+b) (a*val x+e) using 1
    congr 1
    funext y
    congr 1
    ring
  calc
    4 * nz c = 2 * (2 * nz c) := by omega
    _ ≤ 2 * ∑ x : Fin 3, nz (c*val x+b) := Nat.mul_le_mul_left 2 h
    _ = ∑ x : Fin 3, 2 * nz (c*val x+b) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hh x)

theorem square_sharp :
    (∑ x : Fin 3, ∑ y : Fin 3, nz (val x * val y)) = 4 := by decide

structure Bilinear where
  mixed : ℤ
  left : ℤ
  right : ℤ
  constant : ℤ

def Bilinear.eval (f : Bilinear) (x y : ℤ) : ℤ :=
  f.mixed*x*y + f.left*x + f.right*y + f.constant
def Bilinear.add (f g : Bilinear) : Bilinear :=
  ⟨f.mixed+g.mixed,f.left+g.left,f.right+g.right,f.constant+g.constant⟩
def Bilinear.sub (f g : Bilinear) : Bilinear :=
  ⟨f.mixed-g.mixed,f.left-g.left,f.right-g.right,f.constant-g.constant⟩
theorem eval_add (f g : Bilinear) (x y : ℤ) :
    (f.add g).eval x y = f.eval x y + g.eval x y := by simp [Bilinear.eval,Bilinear.add]; ring
theorem eval_sub (f g : Bilinear) (x y : ℤ) :
    (f.sub g).eval x y = f.eval x y - g.eval x y := by simp [Bilinear.eval,Bilinear.sub]; ring
theorem distance (f g : Bilinear) (h : f.mixed ≠ g.mixed) :
    4 ≤ ∑ x : Fin 3, ∑ y : Fin 3, if f.eval (val x) (val y) ≠ g.eval (val x) (val y) then 1 else 0 := by
  have hs := square_support (f.sub g).mixed (f.sub g).left (f.sub g).right (f.sub g).constant
  change _ ≤ ∑ x : Fin 3, ∑ y : Fin 3, nz ((f.sub g).eval (val x) (val y)) at hs
  simp_rw [eval_sub] at hs
  simpa [Bilinear.sub, nz, sub_eq_zero, h] using hs
end TernaryGrid

namespace SpinMass
open Finset TernaryGrid
variable {t k : ℕ}
def vary (e : Pair t) (p : Mask t) (x y : Fin 3) (i : Fin t) : Fin 3 :=
  if i = e.val.1 then x else if i = e.val.2 then y else p i

def interp (f : ℤ → ℤ → ℤ) : Bilinear :=
  ⟨f 1 1 - f 1 0 - f 0 1 + f 0 0, f 1 0 - f 0 0, f 0 1 - f 0 0, f 0 0⟩

def formalEdge (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : ℤ) : ℤ :=
  let z := fun i => if i = e.val.1 then x else if i = e.val.2 then y else sign (p i)
  g.elim 0 (fun u => z u.val.1 * z u.val.2)

theorem interp_edge (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : ℤ) :
    (interp (formalEdge e p g)).eval x y = formalEdge e p g x y ∧
    (interp (formalEdge e p g)).mixed = (if g = some e then 1 else 0) := by
  cases g with
  | none => simp [interp, formalEdge, Bilinear.eval]
  | some u =>
    have hu := u.property
    have he := e.property
    have eqs : u = e ↔ u.val.1 = e.val.1 ∧ u.val.2 = e.val.2 := by
      exact Subtype.ext_iff.trans Prod.ext_iff
    simp only [formalEdge,Option.elim,interp,Bilinear.eval,Option.some.injEq,eqs]
    by_cases h₁ : u.val.1 = e.val.1 <;> by_cases h₂ : u.val.1 = e.val.2 <;>
      by_cases h₃ : u.val.2 = e.val.1 <;> by_cases h₄ : u.val.2 = e.val.2 <;>
      first | (exfalso; omega) | (simp only [if_pos,if_neg,h₁,h₂,h₃,h₄, ne_of_lt he, Ne.symm (ne_of_lt he), ite_self, true_and, false_and, and_true, and_false, ite_true, ite_false]; constructor <;> ring)

theorem formal_semantics (e : Pair t) (p : Mask t) (g : Option (Pair t)) (x y : Fin 3) :
    formalEdge e p g (val x) (val y) = edgeSign g (vary e p x y) := by
  have h (i : Fin t) : (if i = e.val.1 then val x else if i = e.val.2 then val y else sign (p i)) =
      sign (vary e p x y i) := by
    unfold vary
    split_ifs <;> rfl
  cases g with
  | none => rfl
  | some u => exact congrArg₂ (· * ·) (h u.val.1) (h u.val.2)

def polyModel (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) : Bilinear :=
  let f := fun l => interp (formalEdge e p (G l))
  ⟨∑ l, (f l).mixed, ∑ l, (f l).left, ∑ l, (f l).right, ∑ l, (f l).constant⟩
def mult (G : Fin k → Option (Pair t)) (e : Pair t) : ℕ := (univ.filter (fun l => G l = some e)).card
theorem poly_mixed (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) :
    (polyModel e p G).mixed = (mult G e : ℤ) := by
  change (∑ l, (interp (formalEdge e p (G l))).mixed) = _
  simp_rw [(interp_edge e p _ 0 0).2]
  exact sum_boole _ _
theorem poly_eval (e : Pair t) (p : Mask t) (G : Fin k → Option (Pair t)) (x y : Fin 3) :
    (polyModel e p G).eval (val x) (val y) =
    ((reading G (vary e p x y)).factorization 5 : ℤ) - ((reading G (vary e p x y)).factorization 3 : ℤ) := by
  rw [← signed_reading]
  simp only [polyModel, Bilinear.eval, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  exact ((interp_edge e p (G l) (val x) (val y)).1).trans (formal_semantics e p (G l) x y)

theorem four_masks (G H : Fin k → Option (Pair t)) (e : Pair t) (p : Mask t)
    (h : mult G e ≠ mult H e) :
    4 ≤ ∑ x : Fin 3, ∑ y : Fin 3, if reading G (vary e p x y) ≠ reading H (vary e p x y) then 1 else 0 := by
  have hd := TernaryGrid.distance (polyModel e p G) (polyModel e p H) (by simpa [poly_mixed] using h)
  apply le_trans hd
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  simp_rw [poly_eval]
  by_cases hh : reading G (vary e p x y) = reading H (vary e p x y)
  · simp [hh]
  · simp [hh]; split <;> decide

end SpinMass

namespace SpinMass
open Finset
variable {t k : ℕ}

abbrev Away (e : Pair t) := {i : Fin t // i ≠ e.val.1 ∧ i ≠ e.val.2}
def fill (e : Pair t) (r : Away e → Fin 3) (x y : Fin 3) (i : Fin t) : Fin 3 :=
  if h : i = e.val.1 then x else if h' : i = e.val.2 then y else r ⟨i,h,h'⟩

def maskEquiv (e : Pair t) : Mask t ≃ (Away e → Fin 3) × (Fin 3 × Fin 3) where
  toFun p := (fun i => p i.val, p e.val.1, p e.val.2)
  invFun a := fill e a.1 a.2.1 a.2.2
  left_inv p := by
    funext i
    simp only [fill]
    split <;> first | simp_all | split <;> simp_all
  right_inv a := by
    rcases a with ⟨r,x,y⟩
    have hi := ne_of_lt e.property
    simp [fill,hi.symm]
    funext i
    simp [i.property.1,i.property.2]

theorem vary_fill (e : Pair t) (r : Away e → Fin 3) (x y : Fin 3) :
    vary e (fill e r 0 0) x y = fill e r x y := by
  funext i; unfold vary fill; split_ifs <;> rfl

theorem dimensions (e : Pair t) : 3^t = 9 * Fintype.card (Away e → Fin 3) := by
  have h := Fintype.card_congr (maskEquiv e)
  change Fintype.card (Fin t → Fin 3) = _ at h
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,show 3*3=9 by decide,Nat.mul_comm 9] using h

theorem support_sum (e : Pair t) (f : Mask t → ℕ) :
    (∑ p, f p) = ∑ r : Away e → Fin 3, ∑ x : Fin 3, ∑ y : Fin 3, f (fill e r x y) := by
  rw [← (maskEquiv e).symm.sum_comp f, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type]
  rfl

def dist {ι : Type} [Fintype ι] (u v : ι → ℕ) : ℕ :=
  ∑ i, if u i ≠ v i then 1 else 0

theorem full_distance (G H : Fin k → Option (Pair t)) (e : Pair t) (h : mult G e ≠ mult H e) :
    4 * 3^t ≤ 9 * dist (reading G) (reading H) := by
  have hf (r : Away e → Fin 3) := four_masks G H e (fill e r 0 0) h
  simp_rw [vary_fill] at hf
  have hd := Finset.sum_le_sum (s := (univ : Finset (Away e → Fin 3))) (fun r _ => hf r)
  rw [← support_sum e (fun p => if reading G p ≠ reading H p then 1 else 0)] at hd
  simp only [sum_const,card_univ,nsmul_eq_mul] at hd
  change Fintype.card (Away e → Fin 3) * 4 ≤ _ at hd
  rw [dimensions e]
  unfold dist
  omega

def erasures {ι : Type} [Fintype ι] (y : ι → Option ℕ) : ℕ :=
  ∑ i, if y i = none then 1 else 0
def cost {ι : Type} [Fintype ι] (y : ι → Option ℕ) (u : ι → ℕ) : ℕ :=
  ∑ i, if y i ≠ none ∧ y i ≠ some (u i) then 1 else 0

theorem cost_triangle {ι : Type} [Fintype ι] (y : ι → Option ℕ) (u v : ι → ℕ) :
    dist u v ≤ cost y u + cost y v + erasures y := by
  unfold dist cost erasures
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  by_cases h : u i = v i <;> by_cases hh : y i = none <;> by_cases ha : y i = some (u i) <;>
    by_cases hb : y i = some (v i) <;> simp_all

theorem nearest_recovers (G H : Fin k → Option (Pair t)) (y : Mask t → Option ℕ)
    (hc : cost y (reading H) ≤ cost y (reading G))
    (hr : 9 * (2 * cost y (reading G) + erasures y) < 4 * 3^t) :
    ∀ e, mult H e = mult G e := by
  intro e
  by_contra hn
  have hl := full_distance H G e hn
  have hu := cost_triangle y (reading H) (reading G)
  omega

end SpinMass

namespace SparseSampling
open Finset Real

def ind (b : Bool) : ℝ := if b then 1 else 0

theorem exp_quadratic (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1-x+x^2 := by
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
  have hp : 0 ≤ 1-x+x^2 := by nlinarith [sq_nonneg (x-1/2)]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hp
  nlinarith [mul_nonneg hx (sq_nonneg x)]

noncomputable def weight (x : ℝ) (b : Bool) : ℝ :=
  Real.exp ((4/9-x-ind b)*x + x^2/2)

theorem one_step {X : Type} [Fintype X] (b : X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b i)) :
    (∑ i, weight x (b i)) ≤ Fintype.card X := by
  let n : ℝ := Fintype.card X
  let a := (4/9-x)*x+x^2/2
  have exp_le_one : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
  have ht (z : Bool) : weight x z = Real.exp a * (1 - ind z * (1-Real.exp (-x))) := by
    cases z with
    | false => simp [weight,ind,a]
    | true =>
      change Real.exp ((4/9-x-1)*x+x^2/2) = Real.exp a * (1-1*(1-Real.exp (-x)))
      rw [one_mul,sub_sub_cancel,← Real.exp_add]
      congr 1; dsimp [a]; ring
  simp_rw [ht]
  rw [← mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one]
  change Real.exp a * (n - (∑ i, ind (b i)) * (1-Real.exp (-x))) ≤ n
  change 4*n ≤ _ at hd
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hα : n - (∑ i, ind (b i)) * (1-Real.exp (-x)) ≤ n*(1-a) := by
    have hq := exp_quadratic x hx
    have h₁ := mul_le_mul_of_nonneg_right (show 4/9*n ≤ ∑ i, ind (b i) by linarith) (sub_nonneg.mpr exp_le_one)
    have h₂ := mul_le_mul_of_nonneg_left (show x-x^2 ≤ 1-Real.exp (-x) by linarith) (show 0 ≤ 4/9*n by positivity)
    dsimp [a]
    nlinarith [mul_nonneg hn (sq_nonneg x)]
  have hneg := Real.add_one_le_exp (-a)
  calc
    _ ≤ Real.exp a * (n*(1-a)) := mul_le_mul_of_nonneg_left hα (Real.exp_pos _).le
    _ ≤ Real.exp a * (n*Real.exp (-a)) := by gcongr; linarith
    _ = n := by rw [← mul_left_comm,← Real.exp_add]; simp

theorem good_row {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i))
    (w : F → ℝ) (hw : ∀ f, 0 ≤ w f) :
    ∃ i, ∑ f, w f * weight x (b f i) ≤ ∑ f, w f := by
  classical
  by_contra! h
  have ha := Finset.sum_lt_sum_of_nonempty (s := (univ : Finset X)) univ_nonempty (fun i _ => h i)
  rw [show (∑ i, ∑ f, w f * weight x (b f i)) = ∑ f, ∑ i, w f * weight x (b f i) from Finset.sum_comm] at ha
  have hb : (∑ f, ∑ i, w f * weight x (b f i)) ≤ ∑ f, w f * Fintype.card X := by
    apply sum_le_sum
    intro f _
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (one_step _ _ hx (hd f)) (hw f)
  have hc : (∑ i : X, ∑ f, w f) = ∑ f, w f * Fintype.card X := by
    simp [← sum_mul, mul_comm]
  rw [← hc] at hb
  linarith

def hits {X F : Type} (b : F → X → Bool) (s : List X) (f : F) : ℝ :=
  (s.map (fun i => ind (b f i))).sum

noncomputable def score {X F : Type} (b : F → X → Bool) (s : List X) (f : F) (x : ℝ) :=
  Real.exp ((((4/9-x) * s.length - hits b s f)*x) + s.length*x^2/2)

theorem choose_batch {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (x : ℝ) (hx : 0 ≤ x)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i)) (d : ℕ) :
    ∃ s : List X, s.length = d ∧ ∑ f, score b s f x ≤ Fintype.card F := by
  induction d with
  | zero => exact ⟨[],rfl,by simp [score,hits]⟩
  | succ d ih =>
    obtain ⟨s,hs,hh⟩ := ih
    obtain ⟨i,hi⟩ := good_row b x hx hd (fun f => score b s f x) (fun _ => (Real.exp_pos _).le)
    refine ⟨i::s,by simp [hs], ?_⟩
    have he (f : F) : score b (i::s) f x = score b s f x * weight x (b f i) := by
      simp only [score,weight,hits,List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,← Real.exp_add]
      congr 1; ring
    simpa only [he] using hi.trans hh

theorem sparse_batch {X F : Type} [Fintype X] [Nonempty X] [Fintype F]
    (b : F → X → Bool) (s : ℕ) (hs : 0 < s)
    (hd : ∀ f, 4 * (Fintype.card X : ℝ) ≤ 9 * ∑ i, ind (b f i))
    (L : ℕ) (hL : Fintype.card F < 2^L) :
    ∃ batch : List X, batch.length = 2*s^2*L ∧
      ∀ f, (4/9-1/(s:ℝ))*batch.length ≤ hits b batch f := by
  let x : ℝ := 1/(s:ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  obtain ⟨B,hB,hcost⟩ := choose_batch b x hx.le hd (2*s^2*L)
  refine ⟨B,hB,fun f => ?_⟩
  have hscore : score b B f x ≤ Fintype.card F :=
    (Finset.single_le_sum (f := fun z => score b B z x) (fun z _ => (Real.exp_pos _).le) (Finset.mem_univ f)).trans hcost
  have hbound : (Fintype.card F : ℝ) < Real.exp (L:ℝ) := by
    have hh : (Fintype.card F : ℝ) < (2:ℝ)^L := by exact_mod_cast hL
    refine hh.trans_le ?_
    simpa [← Real.exp_nat_mul] using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) Real.exp_one_gt_two.le L)
  have hnorm : (B.length:ℝ)*x^2/2 = L := by
    rw [hB]; dsimp [x]; push_cast; field_simp <;> ring
  unfold score at hscore
  rw [hnorm] at hscore
  have hn := Real.exp_lt_exp.mp (hscore.trans_lt hbound)
  change (4/9-x)*B.length ≤ _
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr h) hx]
end SparseSampling

namespace SpinMass
open Finset SparseSampling
variable {t k : ℕ}
abbrev Model (t k : ℕ) := Fin k → Option (Pair t)
def slotBits (t k : ℕ) := 4 * k * (1 + Nat.log 2 t) + 1
theorem count_models (t k : ℕ) :
    Fintype.card (Model t k × Model t k) < 2^slotBits t k := by
  let b := 1 + Nat.log 2 t
  have ht : t+1 ≤ 2^b := by simpa [b,Nat.add_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
  have hp : Fintype.card (Pair t) ≤ t*t := by
    simpa using Fintype.card_le_of_injective (fun e : Pair t => e.val) Subtype.val_injective
  have ho : Fintype.card (Option (Pair t)) ≤ (2^b)^2 := by
    rw [Fintype.card_option]
    calc
      _ ≤ (t+1)^2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_left ht 2
  have hM : Fintype.card (Model t k) ≤ 2^(b*2*k) := by
    simpa [Model, Fintype.card_fun, pow_mul] using Nat.pow_le_pow_left ho k
  rw [Fintype.card_prod]
  refine (Nat.mul_le_mul hM hM).trans_lt ?_
  rw [← pow_add]
  change 2^_ < 2^(4*k*b+1)
  apply Nat.pow_lt_pow_right (by decide)
  ring_nf; omega

def distinguish (z : Model t k × Model t k) (p : Mask t) : Bool :=
  decide ((∀ e, mult z.1 e = mult z.2 e) ∨ reading z.1 p ≠ reading z.2 p)

theorem ind_case (P : Prop) [Decidable P] : ind (decide P) = ((if P then 1 else 0 : ℕ) : ℝ) := by
  by_cases h : P <;> simp [h,ind]

theorem dist_at (G H : Model t k) (hn : ¬∀ e, mult G e = mult H e) (p : Mask t) :
    ind (distinguish (G,H) p) = ((if reading G p ≠ reading H p then 1 else 0 : ℕ) : ℝ) := by
  unfold distinguish
  simp only [hn,false_or]
  exact ind_case _

theorem distinguish_density (z : Model t k × Model t k) :
    4 * (Fintype.card (Mask t) : ℝ) ≤ 9 * ∑ p, ind (distinguish z p) := by
  by_cases h : ∀ e, mult z.1 e = mult z.2 e
  · have hh (p : Mask t) : ind (distinguish z p) = 1 := by
      have hc : (∀ e, mult z.1 e = mult z.2 e) ∨ reading z.1 p ≠ reading z.2 p := Or.inl h
      unfold distinguish; rw [decide_eq_true hc]; rfl
    simp only [hh,sum_const,card_univ,nsmul_eq_mul,mul_one]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Mask t))]
  · obtain ⟨e,he⟩ := Classical.not_forall.mp h
    have hd := full_distance z.1 z.2 e he
    have hv (p : Mask t) : ind (distinguish z p) = ((if reading z.1 p ≠ reading z.2 p then 1 else 0 : ℕ) : ℝ) := by
      exact dist_at z.1 z.2 h p
    simp_rw [hv,← Nat.cast_sum]
    change 4 * (Fintype.card (Fin t → Fin 3) : ℝ) ≤ _
    simp only [Fintype.card_fun,Fintype.card_fin]
    exact_mod_cast hd

theorem hits_get {X F : Type} (b : F → X → Bool) (l : List X) (f : F) :
    hits b l f = ∑ i : Fin l.length, ind (b f (l.get i)) := by
  rw [← List.sum_ofFn]
  unfold hits
  congr 1
  apply List.ext_getElem
  · simp
  · intros; simp

def rowDist {d : ℕ} (batch : Fin d → Mask t) (G H : Model t k) :=
  dist (fun i => reading G (batch i)) (fun i => reading H (batch i))

theorem short_distance (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ d : ℕ, ∃ batch : Fin d → Mask t, d = 2*s^2*slotBits t k ∧
      ∀ (G H : Model t k) (e : Pair t), mult G e ≠ mult H e →
      (4*s-9)*d ≤ 9*s*rowDist batch G H := by
  obtain ⟨B,hB,hfit⟩ := sparse_batch distinguish s (by omega) distinguish_density (slotBits t k) (count_models t k)
  refine ⟨B.length,B.get,hB,fun G H e he => ?_⟩
  have hh := hfit (G,H)
  rw [hits_get] at hh
  have hn : ¬ ∀ e, mult G e = mult H e := fun z => he (z e)
  have hu (i : Fin B.length) : ind (distinguish (G,H) (B.get i)) =
      ((if reading G (B.get i) ≠ reading H (B.get i) then 1 else 0 : ℕ) : ℝ) := by
    exact dist_at G H hn (B.get i)
  simp_rw [hu,← Nat.cast_sum] at hh
  change _ ≤ (rowDist B.get G H : ℝ) at hh
  have hs' : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  field_simp at hh
  have h₉ : 9 ≤ 4*s := by omega
  exact_mod_cast (show (((4*s-9:ℕ):ℝ)*B.length) ≤ 9*(s:ℝ)*rowDist B.get G H by
    rw [Nat.cast_sub h₉]; push_cast; nlinarith)

theorem short_recovers (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ d : ℕ, ∃ batch : Fin d → Mask t, d = 2*s^2*slotBits t k ∧
    ∀ (G H : Model t k) (y : Fin d → Option ℕ),
      let word := fun (M : Model t k) i => reading M (batch i)
      9*s*(2*cost y (word G)+erasures y) < (4*s-9)*d →
      cost y (word H) ≤ cost y (word G) → ∀ e, mult H e = mult G e := by
  obtain ⟨d,batch,hd,hh⟩ := short_distance t k s hs
  refine ⟨d,batch,hd,fun G H y hr hc e => ?_⟩
  by_contra hn
  have hlo := hh H G e hn
  have htr := cost_triangle y (fun i => reading H (batch i)) (fun i => reading G (batch i))
  dsimp only at hr hc
  have hle := Nat.mul_le_mul_left (9*s) (show rowDist batch H G ≤ 2*cost y (fun i => reading G (batch i))+erasures y by unfold rowDist; omega)
  omega

end SpinMass

namespace SpinMass
open Finset
theorem single_iff {t : ℕ} (e : Pair t) (p : Mask t) :
    obs (some e) p ≠ obs none p ↔ p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 := by
  have h := mass_identity (some e) p
  have h' := mass_identity none p
  have hn := rawprod_pos p
  change 4*obs (some e) p = 2*_ * factor (p e.val.1) (p e.val.2) at h
  change 4*obs none p = 2*_ * 4 at h'
  have he : obs (some e) p = obs none p ↔ factor (p e.val.1) (p e.val.2) = 4 := by
    calc
      _ ↔ 4*obs (some e) p = 4*obs none p := by omega
      _ ↔ _ := by rw [h,h']; exact Nat.mul_right_inj (Nat.mul_pos (by decide) hn).ne'
  rw [ne_eq,he]
  exact (by decide : ∀ a b, ¬factor a b = 4 ↔ a ≠ 0 ∧ b ≠ 0) _ _

theorem exact_distance {t : ℕ} (e : Pair t) :
    9 * dist (obs (some e)) (obs none) = 4 * 3^t := by
  unfold dist
  rw [support_sum e, dimensions e]
  have h (r : Away e → Fin 3) : (∑ x : Fin 3, ∑ y : Fin 3,
      if obs (some e) (fill e r x y) ≠ obs none (fill e r x y) then 1 else 0 : ℕ) = 4 := by
    simp only [single_iff]
    have h₁ (x y) : fill e r x y e.val.1 = x := by simp [fill]
    have h₂ (x y) : fill e r x y e.val.2 = y := by simp [fill,(ne_of_lt e.property).symm]
    simp_rw [h₁,h₂]
    decide
  simp only [h,sum_const,card_univ,nsmul_eq_mul]
  change 9*(Fintype.card (Away e → Fin 3)*4) = _
  ring
end SpinMass

namespace SpinHash
open Finset SpinMass
abbrev Label (t b : ℕ) := Fin t → Fin b

def colorFill {t b : ℕ} (e : Pair t) (r : Away e → Fin b) (x y : Fin b) (i : Fin t) : Fin b :=
  if h : i = e.val.1 then x else if h' : i = e.val.2 then y else r ⟨i,h,h'⟩
def colorEquiv {t b : ℕ} (e : Pair t) : Label t b ≃ (Away e → Fin b) × (Fin b × Fin b) where
  toFun p := (fun i => p i.val, p e.val.1, p e.val.2)
  invFun a := colorFill e a.1 a.2.1 a.2.2
  left_inv p := by
    funext i; simp only [colorFill]
    split <;> first | simp_all | split <;> simp_all
  right_inv a := by
    rcases a with ⟨r,x,y⟩
    simp [colorFill,(ne_of_lt e.property).symm]
    funext i; simp [i.property.1,i.property.2]

def multiplier {t b : ℕ} (e : Pair t) (c : Label t b) : ℝ :=
  if c e.val.1 = c e.val.2 then 2 else 1

theorem moment {t b : ℕ} (e : Pair t) (hb : 0 < b) :
    (∑ c : Label t b, multiplier e c) = (Fintype.card (Label t b) : ℝ)*(1+1/b) := by
  have ht := Fintype.card_congr (colorEquiv (b := b) e)
  let N := Fintype.card (Away e → Fin b)
  change Fintype.card (Label t b) = _ at ht
  simp only [Fintype.card_prod,Fintype.card_fin] at ht
  change Fintype.card (Label t b) = N*(b*b) at ht
  rw [ht,← (colorEquiv (b := b) e).symm.sum_comp (multiplier e),Fintype.sum_prod_type]
  have block (r : Away e → Fin b) : (∑ z : Fin b × Fin b, multiplier e ((colorEquiv e).symm (r,z))) = (b:ℝ)*(b+1) := by
    rw [Fintype.sum_prod_type]
    have hv (x y : Fin b) : multiplier e ((colorEquiv e).symm (r,x,y)) = (1:ℝ) + if x = y then 1 else 0 := by
      change (if colorFill e r x y e.val.1 = colorFill e r x y e.val.2 then (2:ℝ) else 1) = _
      by_cases h : x = y <;> simp [colorFill,(ne_of_lt e.property).symm,h] <;> norm_num
    simp_rw [hv, sum_add_distrib]
    simp; ring
  simp_rw [block]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_mul]
  change (N:ℝ)*(_*_) = _; field_simp <;> ring

def agreements {t b H : ℕ} (f : Fin H → Label t b) (e : Pair t) :=
  (univ.filter (fun i => f i e.val.1 = f i e.val.2)).card

theorem prod_multiplier {t b H : ℕ} (f : Fin H → Label t b) (e : Pair t) :
    (∏ i, multiplier e (f i)) = 2^agreements f e := by
  have hi (i : Fin H) : multiplier e (f i) = (2:ℝ)^(if f i e.val.1 = f i e.val.2 then 1 else 0 : ℕ) := by
    unfold multiplier; split <;> simp_all
  simp_rw [hi]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact sum_boole _ _

theorem multiplicative_bound {b : ℕ} (hb : 0 < b) : (1+1/(b:ℝ))^b ≤ 4 := by
  have h := Real.add_one_le_exp (1/(b:ℝ))
  rw [add_comm] at h
  refine (pow_le_pow_left₀ (by positivity) h b).trans ?_
  rw [← Real.exp_nat_mul]
  have hn : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [show (b:ℝ)*(1/b) = 1 by field_simp]
  linarith [Real.exp_one_lt_three]

theorem hash_family (t b L : ℕ) (hb : 0 < b) (hs : Fintype.card (Pair t) < 2^L) :
    ∃ f : Fin (b*L) → Label t b, ∀ e, agreements f e < 3*L := by
  classical
  let H := b*L
  let X := Label t b
  let n : ℝ := Fintype.card X
  haveI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hm (e : Pair t) :
      (∑ f : Fin H → X, (2:ℝ)^agreements f e) = n^H * (1+1/(b:ℝ))^H := by
    simp_rw [← prod_multiplier]
    rw [← Fintype.prod_sum (fun (_ : Fin H) (c : X) => multiplier e c)]
    simp only [prod_const,card_univ,Fintype.card_fin]
    rw [moment e hb,mul_pow]
  have hbnd : (1+1/(b:ℝ))^H ≤ 4^L := by
    dsimp [H]; rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (multiplicative_bound hb) _
  have hsum : (∑ f : Fin H → X, ∑ e : Pair t, (2:ℝ)^agreements f e) < n^H*2^(3*L) := by
    rw [Finset.sum_comm]
    simp_rw [hm]
    simp only [sum_const,card_univ,nsmul_eq_mul]
    have h' : (Fintype.card (Pair t) : ℝ) < (2:ℝ)^L := by exact_mod_cast hs
    calc
      _ = n^H * ((Fintype.card (Pair t) : ℝ) * (1+1/(b:ℝ))^H) := by ring
      _ ≤ n^H * ((Fintype.card (Pair t) : ℝ) * 4^L) := by gcongr
      _ < n^H * ((2:ℝ)^L * 4^L) := by gcongr
      _ = _ := by rw [← mul_pow,show 3*L = 3 * L by rfl, pow_mul (2:ℝ) 3 L]; norm_num
  by_contra! h
  have hlo (f : Fin H → X) : (2:ℝ)^(3*L) ≤ ∑ e : Pair t, (2:ℝ)^agreements f e := by
    obtain ⟨e,he⟩ := h f
    exact (pow_le_pow_right₀ (by norm_num) he).trans
      (Finset.single_le_sum (f := fun z => (2:ℝ)^agreements f z) (fun _ _ => by positivity) (mem_univ e))
  have hh := Finset.sum_le_sum (s := univ) (fun f _ => hlo f)
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow] at hh
  exact (not_lt_of_ge hh) hsum

end SpinHash

namespace SpinHash
open Finset SpinMass
variable {t b k : ℕ}
def ordered {n : ℕ} (a b : Fin n) : Option (Pair n) :=
  if h : a < b then some ⟨(a,b),h⟩ else
  if h : b < a then some ⟨(b,a),h⟩ else none

theorem ordered_swap {n : ℕ} (a b : Fin n) : ordered a b = ordered b a := by
  unfold ordered
  rcases lt_trichotomy a b with h|h|h <;> simp_all [not_lt_of_ge] <;> omega

theorem ordered_some {n : ℕ} (a b : Fin n) (e : Pair n) :
    ordered a b = some e ↔ (a = e.val.1 ∧ b = e.val.2) ∨ (a = e.val.2 ∧ b = e.val.1) := by
  have he := e.property
  rcases e with ⟨⟨i,j⟩,he'⟩
  change i < j at he
  unfold ordered
  split_ifs with h h' <;> simp only [Option.some.injEq,Subtype.mk.injEq,Prod.mk.injEq,reduceCtorEq]
  all_goals constructor <;> rintro h₀ <;> first | tauto | rcases h₀ with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp_all | omega
  all_goals omega

def project (c : Label t b) (g : Option (Pair t)) : Option (Pair b) :=
  g.bind (fun u => ordered (c u.val.1) (c u.val.2))

def safe (c : Label t b) (a : Fin t × Fin t) := c a.1 = c a.2 → a.1 = a.2

def guards (e : Pair t) (u : Option (Pair t)) : List (Fin t × Fin t) :=
  u.elim [] (fun f => [f.val,(e.val.1,f.val.1),(e.val.1,f.val.2),(e.val.2,f.val.1),(e.val.2,f.val.2)])

def critical (e : Pair t) (G : Model t k) : List (Fin t × Fin t) :=
  e.val :: (List.ofFn fun l => guards e (G l)).flatten

theorem critical_size (e : Pair t) (G : Model t k) : (critical e G).length ≤ 5*k+1 := by
  have hi (l : Fin k) : (guards e (G l)).length ≤ 5 := by cases G l <;> simp [guards]
  simp only [critical,List.length_cons,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  have hh := Finset.sum_le_sum (s := univ) (fun l _ => hi l)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  change (∑ l, (guards e (G l)).length) ≤ k*5 at hh
  simpa [Nat.mul_comm] using Nat.add_le_add_right hh 1

theorem guard_mem (e : Pair t) (G : Model t k) (l : Fin k) {p : Fin t × Fin t}
    (hp : p ∈ guards e (G l)) : p ∈ critical e G := by
  apply List.mem_cons_of_mem
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨l,rfl⟩,hp⟩

theorem ordered_eq {n : ℕ} {a b c d : Fin n} (h : a ≠ b) :
    ordered a b = ordered c d ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  cases h' : ordered a b with
  | none =>
    unfold ordered at h'
    split_ifs at h' <;> simp_all <;> omega
  | some e =>
    have hab := (ordered_some a b e).mp h'
    rw [eq_comm, ordered_some]
    rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> grind

theorem project_preserves {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) :
    ∃ q : Pair b, project c (some e) = some q ∧ mult (fun l => project c (G l)) q = mult G e := by
  have he := hc e.val (by simp [critical])
  have hne : c e.val.1 ≠ c e.val.2 := fun hh => (ne_of_lt e.property) (he hh)
  have hsome : (ordered (c e.val.1) (c e.val.2)).isSome := by
    unfold ordered; split_ifs <;> simp_all <;> omega
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨q,hq,?_⟩
  unfold mult
  congr 1
  apply filter_congr
  intro l _
  cases hu : G l with
  | none => simp [hu,project]
  | some u =>
    have hv (p) (hp : p ∈ guards e (some u)) : safe c p :=
      hc p (guard_mem e G l (hu ▸ hp))
    have h₁ := hv (e.val.1,u.val.1) (by simp [guards])
    have h₂ := hv (e.val.2,u.val.2) (by simp [guards])
    have h₃ := hv (e.val.1,u.val.2) (by simp [guards])
    have h₄ := hv (e.val.2,u.val.1) (by simp [guards])
    simp only [hu,project,Option.bind_some,Option.some.injEq]
    rw [← hq,eq_comm,ordered_eq hne]
    constructor
    · rintro (⟨ha,hb⟩|⟨ha,hb⟩)
      · exact Subtype.ext (Prod.ext (h₁ ha).symm (h₂ hb).symm)
      · have h₅ := h₃ ha; have h₆ := h₄ hb
        change e.val.1 = u.val.2 at h₅; change e.val.2 = u.val.1 at h₆
        have he' := e.property;have hu' := u.property;omega
    · rintro rfl; exact Or.inl ⟨rfl,rfl⟩

theorem tag_project {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (l : Fin k) (m : Mask b) :
    tag (project c (G l)) m = tag (G l) (m ∘ c) := by
  cases hu : G l with
  | none => rfl
  | some u =>
    have hs := hc u.val (guard_mem e G l (hu ▸ (by simp [guards] : u.val ∈ guards e (some u))))
    have hn : c u.val.1 ≠ c u.val.2 := fun hh => (ne_of_lt u.property) (hs hh)
    have symm_factor : ∀ x y, factor x y = factor y x := by decide
    change tag (ordered (c u.val.1) (c u.val.2)) m = _
    unfold ordered; split_ifs with h h'
    · rfl
    · exact symm_factor _ _
    · omega
end SpinHash

namespace SpinHash
open Finset SpinMass
variable {t b k H : ℕ}

def common {n : ℕ} (m : Mask n) : ℕ := 2 * ∏ i, raw (m i)
def pattern {n : ℕ} (M : Model n k) (m : Mask n) := ∏ l, tag (M l) m
theorem common_pos {n : ℕ} (m : Mask n) : 0 < common m := Nat.mul_pos (by decide) (rawprod_pos m)
theorem scaled {n : ℕ} (M : Model n k) (m : Mask n) :
    4^k * reading M m = (common m)^k * pattern M m := by
  have h := Finset.prod_congr (s₁ := (univ : Finset (Fin k))) rfl (fun l _ => mass_identity (M l) m)
  simpa [Finset.prod_mul_distrib,reading,pattern,common] using h

def prediction (c : Label t b) (M : Model b k) (m : Mask b) :=
  (common (m ∘ c))^k * pattern M m
theorem prediction_exact {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (m : Mask b) :
    prediction c (fun l => project c (G l)) m = 4^k * reading G (m ∘ c) := by
  rw [scaled]; unfold prediction pattern; simp_rw [tag_project hc]

theorem prediction_eq_iff (c : Label t b) (M N : Model b k) (m : Mask b) :
    prediction c M m = prediction c N m ↔ reading M m = reading N m := by
  have hc := Nat.pow_pos (common_pos m) (n := k)
  have hc' := Nat.pow_pos (common_pos (m ∘ c)) (n := k)
  unfold prediction
  rw [Nat.mul_right_inj hc'.ne']
  calc
    _ ↔ (common m)^k * pattern M m = (common m)^k * pattern N m := (Nat.mul_right_inj hc.ne').symm
    _ ↔ _ := by rw [← scaled,← scaled,Nat.mul_right_inj (by positivity : (4:ℕ)^k ≠ 0)]

noncomputable def failures (f : Fin H → Label t b) (pairs : List (Fin t × Fin t)) : Finset (Fin H) := by
  classical exact univ.filter (fun i => ¬ ∀ p ∈ pairs, safe (f i) p)

theorem failure_bound (f : Fin H → Label t b) (L : ℕ) (hf : ∀ e, agreements f e ≤ L)
    (pairs : List (Fin t × Fin t)) : (failures f pairs).card ≤ L * pairs.length := by
  classical
  induction pairs with
  | nil => simp [failures]
  | cons p ps ih =>
    let bad := univ.filter (fun i => ¬safe (f i) p)
    have hsub : failures f (p::ps) ⊆ bad ∪ failures f ps := by
      intro i hi
      simp only [failures,mem_filter,mem_univ,true_and] at hi
      by_cases h : safe (f i) p
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,fun hz => hi (by simpa [h] using hz)⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hb' : bad.card ≤ L := by
      rcases lt_trichotomy p.1 p.2 with h|h|h
      · have hi : bad ⊆ univ.filter (fun i => f i p.1 = f i p.2) := by
          intro i hz; simp [bad,safe,h.ne] at hz; simpa using hz
        exact (card_le_card hi).trans (hf ⟨p,h⟩)
      · simp [bad,safe,h]
      · have hi : bad ⊆ univ.filter (fun i => f i p.2 = f i p.1) := by
          intro i hz; simp [bad,safe,h.ne.symm] at hz; simpa using hz.symm
        exact (card_le_card hi).trans (hf ⟨(p.2,p.1),h⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem protected_count (f : Fin H → Label t b) (L : ℕ) (hf : ∀ e, agreements f e ≤ L)
    (e : Pair t) (G : Model t k) :
    (failures f (critical e G)).card ≤ L*(5*k+1) :=
  (failure_bound f L hf _).trans (Nat.mul_le_mul_left L (critical_size e G))

theorem cost_scaled {I : Type} [Fintype I] (y : I → Option ℕ) (f : I → ℕ) (a : ℕ) (ha : 0 < a) :
    cost (fun i => (y i).map (a*·)) (fun i => a*f i) = cost y f := by
  unfold cost
  apply sum_congr rfl
  intro i _
  cases hi : y i with
  | none => simp [hi]
  | some n => simp [hi,Nat.mul_right_inj ha.ne']

theorem erasures_scaled {I : Type} [Fintype I] (y : I → Option ℕ) (a : ℕ) :
    erasures (fun i => (y i).map (a*·)) = erasures y := by simp [erasures]
end SpinHash

namespace SpinHash
open Finset SpinMass
variable {t b k I : ℕ}
def blockWord (c : Label t b) (m : Fin I → Mask b) (G : Model t k) (j : Fin I) := reading G (m j ∘ c)

def priced (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ)
    (M : Model b k) : ℕ := if ∃ q, project c (some e) = some q ∧ mult M q = a then
      cost (fun j => (y j).map ((4:ℕ)^k*·)) (fun j => prediction c M (m j)) else I

noncomputable def price (k : ℕ) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ) :=
  (univ : Finset (Model b k)).inf' univ_nonempty (priced c m e a y)

theorem cost_cap {d : ℕ} (y : Fin d → Option ℕ) (f : Fin d → ℕ) : cost y f ≤ d := by
  unfold cost
  have hh := sum_le_sum (s := (univ : Finset (Fin d))) (f := fun i => if y i ≠ none ∧ y i ≠ some (f i) then 1 else 0) (g := fun _ => 1) (fun i _ => by split <;> decide)
  simpa using hh

theorem price_cap (k : ℕ) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ) :
    price k c m e a y ≤ I := by
  unfold price
  apply (inf'_le (fun M : Model b k => priced c m e a y M) (mem_univ (fun _ => none))).trans
  unfold priced;split
  · exact cost_cap _ _
  · rfl

theorem price_true {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (m : Fin I → Mask b) (y : Fin I → Option ℕ) :
    price k c m e (mult G e) y ≤ cost y (blockWord c m G) := by
  let M := fun l => project c (G l)
  have hh : ∃ q, project c (some e) = some q ∧ mult M q = mult G e := project_preserves hc
  have hp (j : Fin I) : prediction c M (m j) = 4^k * blockWord c m G j := prediction_exact hc _
  have h := inf'_le (s := (univ : Finset (Model b k))) (priced c m e (mult G e) y) (mem_univ M)
  change price k c m e (mult G e) y ≤ _ at h
  simpa only [priced,if_pos hh,hp,cost_scaled _ _ _ (by positivity : 0 < (4:ℕ)^k)] using h

theorem price_false {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (s : ℕ) (a : ℕ) (ha : a ≠ mult G e)
    (m : Fin I → Mask b) (y : Fin I → Option ℕ)
    (hsep : ∀ (M N : Model b k) (q : Pair b), mult M q ≠ mult N q →
      (8*s-9)*I ≤ 18*s*rowDist m M N) :
    (8*s-9)*I ≤ 18*s*(price k c m e a y + cost y (blockWord c m G) + erasures y) := by
  obtain ⟨M,_,hM⟩ := exists_mem_eq_inf' (s := (univ : Finset (Model b k))) univ_nonempty (priced c m e a y)
  change price k c m e a y = _ at hM
  rw [hM];unfold priced
  split
  · rename_i h
    obtain ⟨q,hq,hm⟩ := h
    let N := fun l => project c (G l)
    obtain ⟨q',hq',hn⟩ := project_preserves hc
    have heq : q' = q := Option.some.inj (hq'.symm.trans hq)
    subst q'
    have hd := hsep M N q (by change mult M q ≠ mult (fun l => project c (G l)) q; omega)
    have hcompare : rowDist m M N = SpinMass.dist (fun j => prediction c M (m j)) (fun j => prediction c N (m j)) := by
      unfold rowDist SpinMass.dist
      simp only [ne_eq,prediction_eq_iff]
    rw [hcompare] at hd
    let yy := fun j => (y j).map ((4:ℕ)^k*·)
    have htri := cost_triangle yy (fun j => prediction c M (m j)) (fun j => prediction c N (m j))
    have hpred (j) : prediction c N (m j) = 4^k * blockWord c m G j := prediction_exact hc _
    have hcst : cost yy (fun j => prediction c N (m j)) = cost y (blockWord c m G) := by
      simp_rw [hpred];exact cost_scaled _ _ _ (by positivity)
    rw [hcst,show erasures yy = erasures y from erasures_scaled _ _] at htri
    exact hd.trans (Nat.mul_le_mul_left _ htri)
  · exact Nat.mul_le_mul (by omega) (by omega)

end SpinHash

namespace SpinHash
open Finset SpinMass
variable {t b k H I : ℕ}

def totalErrors (f : Fin H → Label t b) (m : Fin I → Mask b)
    (G : Model t k) (y : Fin H → Fin I → Option ℕ) :=
  ∑ i, cost (y i) (blockWord (f i) m G)
def totalLost (y : Fin H → Fin I → Option ℕ) := ∑ i, erasures (y i)
noncomputable def totalPrice (k : ℕ) (f : Fin H → Label t b) (m : Fin I → Mask b)
    (e : Pair t) (a : ℕ) (y : Fin H → Fin I → Option ℕ) :=
  ∑ i, price k (f i) m e a (y i)

theorem aggregate (s : ℕ) (hs : 3 ≤ s) (f : Fin H → Label t b) (m : Fin I → Mask b)
    (G : Model t k) (e : Pair t) (y : Fin H → Fin I → Option ℕ)
    (hsep : ∀ (M N : Model b k) (q : Pair b), mult M q ≠ mult N q → (8*s-9)*I ≤ 18*s*rowDist m M N)
    (hf : 4*s*(failures f (critical e G)).card ≤ H)
    (hr : 9*s*(2*totalErrors f m G y+totalLost y) < (4*s-9)*(H*I)) :
    ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) y < totalPrice k f m e a y := by
  classical
  intro a ha
  let bad := failures f (critical e G)
  let z := fun i : Fin H => if i ∈ bad then 1 else 0
  have hz : ∑ i, z i = bad.card := by simp [z]
  have good (i : Fin H) (hi : i ∉ bad) : ∀ p ∈ critical e G, safe (f i) p := by
    simpa [bad,failures] using hi
  let E := totalErrors f m G y
  let D := totalLost y
  let T := totalPrice k f m e (mult G e) y
  let F := totalPrice k f m e a y
  have htrue (i : Fin H) : price k (f i) m e (mult G e) (y i) ≤ cost (y i) (blockWord (f i) m G) + I*z i := by
    by_cases hi : i ∈ bad
    · simp [z,hi]; have hh := price_cap k (f i) m e (mult G e) (y i); omega
    · simpa [z,hi] using price_true (good i hi) m (y i)
  have ht := sum_le_sum (s := univ) (fun i _ => htrue i)
  rw [sum_add_distrib,← mul_sum,hz] at ht
  change T ≤ E + I * bad.card at ht
  let A := (8*s-9)*I
  have hfalse (i : Fin H) : A ≤ 18*s*(price k (f i) m e a (y i) +
      cost (y i) (blockWord (f i) m G) + erasures (y i)) + A*z i := by
    by_cases hi : i ∈ bad
    · simp [z,hi]
    · simpa [A,z,hi] using price_false (good i hi) s a ha m (y i) hsep
  have ht' := sum_le_sum (s := univ) (fun i _ => hfalse i)
  simp only [sum_add_distrib,← mul_sum,hz,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at ht'
  change H*A ≤ 18*s*(F+E+D)+A*bad.card at ht'
  change 4*s*bad.card ≤ H at hf
  change 9*s*(2*E+D) < (4*s-9)*(H*I) at hr
  change T < F
  by_contra! hn
  have hupper := Nat.mul_le_mul_left (18*s) (show F+E+D ≤ 2*E+D+I*bad.card by omega)
  have hbad := Nat.mul_le_mul_right (9*I) hf
  have hgap := Nat.mul_lt_mul_of_pos_left hr (by decide : 0 < 2)
  have hx : 8*s-9+9=8*s := by omega
  have hy : 4*s-9+9=4*s := by omega
  have hA := congrArg (fun n : ℕ => n * (H*I)) hx
  have hB := congrArg (fun n : ℕ => n * (H*I)) hy
  have hsmall := Nat.mul_le_mul_right (I*bad.card) (show 8*s-9 ≤ 8*s by omega)
  dsimp only [A] at ht'
  nlinarith

end SpinHash

namespace SpinHash
open Finset SpinMass

def colors (k s : ℕ) := 128*((k+1)*s)
def outerL (t : ℕ) := 2*(1+Nat.log 2 t)
def outer (t k s : ℕ) := colors k s * outerL t
def inner (k s : ℕ) := 2*(2*s)^2 * slotBits (colors k s) k

theorem log_colors (k s : ℕ) (hs : 0 < s) : Nat.log 2 (colors k s) ≤ 7+Nat.log 2 ((k+1)*s) := by
  let x := (k+1)*s
  have hx : 0 < x := Nat.mul_pos (by omega) hs
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  have hh := Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2^7)
  rw [← pow_add] at hh
  have hlt := Nat.log_lt_of_lt_pow (b := 2) (by dsimp [colors]; positivity : colors k s ≠ 0)
    (show colors k s < 2^(7+(Nat.log 2 x).succ) from hh)
  change Nat.log 2 (colors k s) ≤ 7+Nat.log 2 x;omega

theorem query_budget (t k s : ℕ) (hs : 0 < s) :
    outer t k s * inner k s ≤ 67584*(k+1)^2*s^3*(1+Nat.log 2 ((k+1)*s))*(1+Nat.log 2 t) := by
  have hl := log_colors k s hs
  let u := Nat.log 2 ((k+1)*s)
  have ha : slotBits (colors k s) k ≤ 33*(k+1)*(1+u) := by
    unfold slotBits
    change Nat.log 2 (colors k s) ≤ 7+u at hl
    have h := Nat.mul_le_mul_left (4*k) (Nat.add_le_add_left hl 1)
    nlinarith
  have hb := Nat.mul_le_mul_left (outer t k s*(2*(2*s)^2)) ha
  change outer t k s * (2*(2*s)^2*slotBits (colors k s) k) ≤ _
  unfold outer colors outerL at *
  dsimp [u] at *
  nlinarith

theorem local_design (t k s : ℕ) (hs : 3 ≤ s) :
    ∃ (f : Fin (outer t k s) → Label t (colors k s))
      (m : Fin (inner k s) → Mask (colors k s)),
      ∀ (G : Model t k) (e : Pair t) (y : Fin (outer t k s) → Fin (inner k s) → Option ℕ),
      9*s*(2*totalErrors f m G y + totalLost y) < (4*s-9)*(outer t k s * inner k s) →
      ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) y < totalPrice k f m e a y := by
  let b := colors k s
  let L := outerL t
  have hb : 0 < b := by dsimp [b,colors]; positivity
  have hnum : Fintype.card (Pair t) < 2^L := by
    have hp : Fintype.card (Pair t) ≤ t*t := by
      simpa using Fintype.card_le_of_injective (fun e : Pair t => e.val) Subtype.val_injective
    have ht := Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
    have hsq : t*t < 2^(Nat.log 2 t).succ * 2^(Nat.log 2 t).succ := by nlinarith [Nat.mul_le_mul (show t+1 ≤ 2^(Nat.log 2 t).succ from ht) (show t+1 ≤ 2^(Nat.log 2 t).succ from ht)]
    dsimp [L,outerL];rw [two_mul, pow_add]
    simpa [Nat.add_comm 1] using hp.trans_lt hsq
  obtain ⟨f,hf⟩ := hash_family t b L hb hnum
  obtain ⟨d,m,hd,hm⟩ := short_distance b k (2*s) (by omega)
  subst d
  refine ⟨f,m,fun G e y hr => ?_⟩
  apply aggregate s hs f m G e y _ _ hr
  · intro M N q hn
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm M N q hn
  · have hh := protected_count f (3*L) (fun e => (hf e).le) e G
    have h := Nat.mul_le_mul_left (4*s) hh
    change 4*s*(failures f (critical e G)).card ≤ b*L
    apply h.trans
    dsimp [b,colors]; nlinarith

end SpinHash

namespace SpinCircuit
open PEqualNP.CircuitLowerBounds
def allowed (g : Gate) : Prop := ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)
def legal (n : ℕ) (p : List Gate) : Prop :=
  ∀ j (h : j < p.length), allowed p[j] ∧ ∀ i ∈ p[j].inputs, i < n+j
def run (p : List Gate) (w : List Bool) := p.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w
theorem run_append (p q : List Gate) (w : List Bool) : run (p++q) w = run q (run p w) := List.foldl_append ..
theorem extends_run (p : List Gate) (w : List Bool) : w <+: run p w := by
  induction p generalizing w with
  | nil => rfl
  | cons g p ih => exact (List.prefix_append w _).trans (ih _)
theorem run_length (p : List Gate) (w : List Bool) : (run p w).length = w.length+p.length := by
  induction p generalizing w with
  | nil => simp [run]
  | cons g p ih => change (run p (w ++ [_])).length = _; rw [ih]; simp; omega
theorem old_wire (p : List Gate) {w : List Bool} {i : ℕ} (h : i < w.length) :
    (run p w).getD i false = w.getD i false := by
  obtain ⟨q,hq⟩ := extends_run p w
  rw [← hq,List.getD_append _ _ _ _ h]
theorem legal_append {n : ℕ} {p q : List Gate} (hp : legal n p) (hq : legal (n+p.length) q) : legal n (p++q) := by
  intro j hj
  by_cases h : j < p.length
  · simpa only [List.getElem_append_left h] using hp j h
  · have hj' : j-p.length < q.length := by simp at hj;omega
    rw [List.getElem_append_right (by omega)]
    have hh := hq _ hj'
    refine ⟨hh.1,fun i hi => ?_⟩
    have := hh.2 i hi;omega

theorem circuit_legal {n : ℕ} {p : List Gate} (hp : legal n p) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨p,0⟩ ∧ ∀ a ∈ p, allowed a := by
  constructor
  · intro j hj i hi
    apply (hp j hj).2 i
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi
  · intro a ha
    obtain ⟨j,h,hj⟩ := List.getElem_of_mem ha
    exact hj ▸ (hp j h).1

variable {X : Type}
def built (n : ℕ) (base : X → List Bool) (f : X → Bool) (B : ℕ) : Prop :=
  ∀ M, n ≤ M → ∃ (p : List Gate) (o : ℕ), legal M p ∧ p.length ≤ B ∧ o < M+p.length ∧
  ∀ x w, w.length=M → base x <+: w → (run p w).getD o false = f x

theorem weaken {n B C : ℕ} {base : X → List Bool} {f : X → Bool} (h : built n base f B) (hh : B ≤ C) :
    built n base f C := by
  intro M hm
  obtain ⟨p,o,hp,hl,ho,he⟩ := h M hm
  exact ⟨p,o,hp,hl.trans hh,ho,he⟩

theorem read_input {n : ℕ} (base : X → List Bool) (hlen : ∀ x, (base x).length = n) (i : Fin n) :
    built n base (fun x => (base x).getD i false) 0 := by
  intro M hM
  refine ⟨[],i,by intro j h; simp at h,by simp,by simpa using i.isLt.trans_le hM,?_⟩
  intro x w hw h
  obtain ⟨v,rfl⟩ := h
  exact List.getD_append _ _ _ _ (by rw [hlen];exact i.isLt)

theorem many {n B : ℕ} (base : X → List Bool) (fs : List (X → Bool))
    (hf : ∀ f ∈ fs, built n base f B) (M : ℕ) (hm : n ≤ M) :
    ∃ (p : List Gate) (os : List ℕ), legal M p ∧ p.length ≤ fs.length*B ∧ os.length=fs.length ∧
    (∀ o ∈ os, o < M+p.length) ∧ ∀ x w, w.length=M → base x <+: w →
    (os.map fun o => (run p w).getD o false) = fs.map (fun f => f x) := by
  induction fs generalizing M with
  | nil => exact ⟨[],[],by intro j h; simp at h,by simp,rfl,by simp,by simp⟩
  | cons f fs ih =>
    obtain ⟨p,o,hp,hl,ho,he⟩ := hf f List.mem_cons_self M hm
    obtain ⟨q,os,hq,hql,hos,hob,hev⟩ := ih (fun f h => hf f (List.mem_cons_of_mem _ h)) (M+p.length) (by omega)
    refine ⟨p++q,o::os,legal_append hp hq,?_,by simp [hos],?_,?_⟩
    · simp [Nat.add_mul];omega
    · intro j hj
      rcases List.mem_cons.mp hj with rfl|hj
      · simp;omega
      · simpa [Nat.add_assoc] using hob j hj
    · intro x w hw hh
      have ww : (run p w).length=M+p.length := by rw [run_length,hw]
      simp only [run_append,List.map_cons,old_wire q (ww ▸ ho),he x w hw hh,
        hev x (run p w) ww (hh.trans (extends_run p w))]

end SpinCircuit

namespace SpinCircuit
open PEqualNP.CircuitLowerBounds
variable {X : Type}
theorem indexed {n B l : ℕ} {base : X → List Bool} (fs : Fin l → X → Bool)
    (hf : ∀ i, built n base (fs i) B) (M : ℕ) (hm : n ≤ M) :
    ∃ (p : List Gate) (o : Fin l → ℕ), legal M p ∧ p.length ≤ l*B ∧
    (∀ i, o i < M+p.length) ∧ ∀ x w, w.length=M → base x <+: w →
    ∀ i, (run p w).getD (o i) false = fs i x := by
  obtain ⟨p,os,hp,hl,hos,hob,hev⟩ := many base (List.ofFn fs)
    (fun f h => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h;exact hf i) M hm
  simp only [List.length_ofFn] at hl hos
  let o := fun i : Fin l => os[i.val]'(hos.symm ▸ i.isLt)
  refine ⟨p,o,hp,hl,fun i => hob _ (List.getElem_mem ..),?_⟩
  intro x w hw hh i
  have h := congrArg (fun s : List Bool => s[i.val]?) (hev x w hw hh)
  have hi : i.val < os.length := by rw [hos];exact i.isLt
  simpa [List.getElem?_map,List.getElem?_eq_getElem hi,i.isLt,o] using h

def cell (M u v z : ℕ) : List Gate := [⟨.and,[u,v]⟩,⟨.or,[z,M]⟩]
theorem cell_legal {M u v z : ℕ} (hu : u < M) (hv : v < M) (hz : z < M) : legal M (cell M u v z) := by
  intro j hj
  have hl : j < 2 := hj
  interval_cases j <;> simp [cell,allowed] <;> omega
theorem cell_eval {M u v z : ℕ} (w : List Bool) (hw : w.length=M) (hz : z<M) :
    (run (cell M u v z) w).getD (M+1) false = (w.getD z false || (w.getD u false && w.getD v false)) := by
  subst M
  have h (ts : List Bool) : (w ++ ts)[z]?.getD false = w[z]?.getD false := by rw [List.getElem?_append_left hz]
  simp [run,cell,GateOp.eval,h,List.getD_eq_getElem?_getD]

def valAt (w : List Bool) (i : ℕ) := w.getD i false
theorem cell_built {n : ℕ} {base : X → List Bool} (len : ∀ x, (base x).length=n)
    (u v z : Fin n) :
    built n base (fun x => (base x).getD z false || ((base x).getD u false && (base x).getD v false)) 2 := by
  intro M hM
  refine ⟨cell M u v z,M+1,cell_legal (u.isLt.trans_le hM) (v.isLt.trans_le hM) (z.isLt.trans_le hM),by rfl,by change M+1<M+2;omega,?_⟩
  intro x w hw h
  rw [cell_eval w hw (z.isLt.trans_le hM)]
  obtain ⟨v',rfl⟩ := h
  simp only [List.getD_append _ _ _ _ (show z.val < (base x).length by rw [len];exact z.isLt),
    List.getD_append _ _ _ _ (show u.val < (base x).length by rw [len];exact u.isLt),
    List.getD_append _ _ _ _ (show v.val < (base x).length by rw [len];exact v.isLt)]

def ones (fs : List ℕ) (w : List Bool) := (fs.map (fun i => w.getD i false)).count true

theorem unary (n D : ℕ) (hn : 2 ≤ n) (ids : List ℕ) (hi : ∀ i ∈ ids, i < n) :
    ∃ (p : List Gate) (o : Fin (D+1) → ℕ), legal n p ∧ p.length ≤ ids.length*((D+1)*2) ∧
    (∀ j, o j < n+p.length) ∧ ∀ w : List Bool, w.length=n → w.getD 0 false=false → w.getD 1 false=true →
    ∀ j : Fin (D+1), (run p w).getD (o j) false = decide (j.val ≤ ones ids w) := by
  induction ids with
  | nil =>
    refine ⟨[],fun j => if j.val=0 then 1 else 0,by intro j h;simp at h,by simp,?_,?_⟩
    · intro j; dsimp only; split <;> simp <;> omega
    · intro w hw h0 h1 j
      by_cases hj : j.val=0 <;> simp [run,ones,hj] <;> assumption
  | cons u us ih =>
    obtain ⟨p,o,hp,hl,ho,he⟩ := ih (fun i h => hi i (List.mem_cons_of_mem _ h))
    let M := n+p.length
    let B := {w : List Bool // w.length=M}
    let b : B → List Bool := Subtype.val
    let prev (j : Fin (D+1)) : Fin (D+1) := ⟨j.val-1,by omega⟩
    let fs := fun (j : Fin (D+1)) (w : B) =>
      w.val.getD (o j) false || (w.val.getD u false && w.val.getD (o (prev j)) false)
    have hu := hi u List.mem_cons_self
    have hb (j) : built M b (fs j) 2 :=
      cell_built (fun w : B => w.property) ⟨u,by dsimp [M];omega⟩ ⟨o (prev j),ho _⟩ ⟨o j,ho j⟩
    obtain ⟨q,z,hq,hlq,hz,hev⟩ := indexed fs hb M le_rfl
    refine ⟨p++q,z,legal_append hp hq,?_,fun j => by simpa [M,Nat.add_assoc] using hz j,?_⟩
    · simp only [List.length_append,List.length_cons]
      exact (Nat.add_le_add hl hlq).trans_eq (by ring)
    · intro w hw h0 h1 j
      have hlen : (run p w).length=M := by rw [run_length,hw]
      rw [run_append,hev ⟨run p w,hlen⟩ (run p w) hlen (by rfl) j]
      change ((run p w).getD (o j) false || ((run p w).getD u false && (run p w).getD (o (prev j)) false)) = _
      rw [he w hw h0 h1 j,he w hw h0 h1 (prev j),old_wire p (hw ▸ hu)]
      change (_ || (_ && decide (j.val-1 ≤ ones us w))) = _
      cases hbit : w.getD u false <;> simp [ones,List.count_cons,List.getD_eq_getElem?_getD] at hbit ⊢ <;> simp_all <;> omega

end SpinCircuit

namespace SpinCircuit
open Finset PEqualNP.CircuitLowerBounds
structure Encoding (X : Type) (n : ℕ) where
  base : X → List Bool
  length : ∀ x, (base x).length = n
  enough : 2 ≤ n
  zero : ∀ x, (base x).getD 0 false=false
  one : ∀ x, (base x).getD 1 false=true

variable {X : Type} {n : ℕ} (E : Encoding X n)
def level (U r : ℕ) (f : X → Bool) := built n E.base f (U^r)

theorem constant (b : Bool) : built n E.base (fun _ => b) 0 := by
  cases b with
  | false =>
    have h := read_input E.base E.length (⟨0,by have := E.enough;omega⟩ : Fin n)
    simpa only [Fin.val_mk,E.zero] using h
  | true =>
    have h := read_input E.base E.length (⟨1,by have := E.enough;omega⟩ : Fin n)
    simpa only [Fin.val_mk,E.one] using h

theorem bool_not {B : ℕ} {f : X → Bool} (h : built n E.base f B) : built n E.base (fun x => !f x) (B+1) := by
  intro M hM
  obtain ⟨p,o,hp,hl,ho,he⟩ := h M hM
  let q : List Gate := [⟨.not,[o]⟩]
  have hq : legal (M+p.length) q := by
    intro j hj
    have hj' : j<1 := hj
    have : j=0 := by omega
    subst j;simp [q,allowed,ho]
  refine ⟨p++q,M+p.length,legal_append hp hq,by simp [q];omega,by simp [q,Nat.add_assoc],?_⟩
  intro x w hw hh
  have hv : (run p w).length=M+p.length := by rw [run_length,hw]
  change _ = !f x
  rw [run_append,← hv,← he x w hw hh]
  simp [run,q,GateOp.eval]

def onCount {l : ℕ} (f : Fin l → X → Bool) (x : X) : ℕ := ∑ i, (f i x).toNat

theorem threshold {l B : ℕ} (fs : Fin l → X → Bool) (hf : ∀ i, built n E.base (fs i) B) (a : ℕ) :
    built n E.base (fun x => decide (a ≤ onCount fs x)) (l*B + l*((l+1)*2)) := by
  by_cases ha : a ≤ l
  · intro M hM
    obtain ⟨p,o,hp,hl,ho,he⟩ := indexed fs hf M hM
    let J := M+p.length
    have hvalid (i) (hi : i ∈ List.ofFn o) : i<J := by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi;exact ho j
    obtain ⟨q,z,hq,hlq,hz,hev⟩ := unary J l (by dsimp [J];have := E.enough;omega) (List.ofFn o) hvalid
    let j : Fin (l+1) := ⟨a,by omega⟩
    refine ⟨p++q,z j,legal_append hp hq,?_,by simpa [J,Nat.add_assoc] using hz j,?_⟩
    · simpa using Nat.add_le_add hl hlq
    · intro x w hw hprefix
      have hv : (run p w).length=J := by rw [run_length,hw]
      have old (i : ℕ) (hi : i<n) : (run p w).getD i false = (E.base x).getD i false := by
        obtain ⟨ts,ht⟩ := hprefix.trans (extends_run p w)
        rw [← ht,List.getD_append _ _ _ _ (by rw [E.length];exact hi)]
      rw [run_append,hev _ hv ((old 0 (by have := E.enough;omega)).trans (E.zero _))
        ((old 1 (by have := E.enough;omega)).trans (E.one _)) j]
      have hx : ones (List.ofFn o) (run p w) = onCount fs x := by
        unfold ones onCount
        rw [List.map_ofFn]
        have hh : (fun j => (run p w).getD (o j) false) = fun j => fs j x := funext (he x w hw hprefix)
        change (List.ofFn (fun j => (run p w).getD (o j) false)).count true = _
        rw [hh,← List.sum_ofFn]
        have hcount (s : List Bool) : s.count true = (s.map Bool.toNat).sum := by
          induction s with
          | nil => rfl
          | cons u us ih => cases u <;> simp [List.count_cons,ih,Nat.add_comm]
        rw [hcount,List.map_ofFn];rfl
      rw [hx]
  · have hx (x : X) : ¬ a ≤ onCount fs x := by
      have hh := sum_le_sum (s := (univ : Finset (Fin l))) (g := fun _ => 1) (fun i _ => Bool.toNat_le (fs i x))
      have hl : onCount fs x ≤ l := by simpa [onCount] using hh
      omega
    simp only [hx,decide_false]
    exact weaken (constant E false) (Nat.zero_le _)

theorem lift_level {U r v : ℕ} (hU : 1 ≤ U) (hv : r≤v) {f : X→Bool} (hf : level E U r f) : level E U v f :=
  weaken hf (Nat.pow_le_pow_right hU hv)
theorem level_const (U r : ℕ) (b : Bool) : level E U r (fun _ => b) := weaken (constant E b) (Nat.zero_le _)
theorem level_not {U r : ℕ} (hU : 4 ≤ U) {f : X→Bool} (hf : level E U r f) : level E U (r+1) (fun x => !f x) := by
  apply weaken (bool_not E hf)
  rw [pow_succ]
  have hp : 0 < U^r := by positivity
  nlinarith
theorem level_threshold {U r l : ℕ} (hU : 4 ≤ U) (hl : l ≤ U) (fs : Fin l → X → Bool)
    (hf : ∀ i, level E U r (fs i)) (a : ℕ) : level E U (r+4) (fun x => decide (a ≤ onCount fs x)) := by
  apply weaken (threshold E fs hf a)
  have hh := Nat.mul_le_mul_right (U^r) hl
  have hg := Nat.mul_le_mul hl (Nat.mul_le_mul_right 2 (Nat.add_le_add_right hl 1))
  have hp : 1 ≤ U^r := Nat.one_le_pow _ _ (by omega)
  rw [pow_add]
  have hs : 4 ≤ U*U := by nlinarith
  have h₁ : U + U*((U+1)*2) ≤ U^4 := by
    have h := Nat.mul_le_mul_left (U*U) hs
    nlinarith
  have h₂ := Nat.mul_le_mul_left (U*((U+1)*2)) hp
  have h₃ := Nat.mul_le_mul_left (U^r) h₁
  nlinarith
end SpinCircuit

namespace SpinCircuit
open Finset
variable {X : Type} {n : ℕ} (E : Encoding X n)
noncomputable def gateP (U r : ℕ) (P : X → Prop) : Prop := by
  classical exact level E U r (fun x => decide (P x))

theorem of_bool {U r : ℕ} {P : X → Prop} {f : X → Bool} (h : level E U r f) (he : ∀ x, f x = true ↔ P x) : gateP E U r P := by
  classical
  unfold gateP
  convert h using 1
  funext x;apply Bool.eq_iff_iff.mpr;simpa using (he x).symm

theorem to_bool {U r : ℕ} {P : X → Prop} {f : X → Bool} (h : gateP E U r P) (he : ∀ x, f x = true ↔ P x) : level E U r f := by
  classical
  unfold gateP at h
  convert h using 1
  funext x;apply Bool.eq_iff_iff.mpr;simpa using he x

theorem gate_const (U r : ℕ) (P : Prop) : gateP E U r (fun _ => P) := by
  classical
  exact level_const E U r (decide P)

theorem gate_not {U r : ℕ} (hU : 4 ≤ U) {P : X → Prop} (h : gateP E U r P) :
    gateP E U (r+1) (fun x => ¬P x) := by
  classical
  simpa only [gateP,decide_not] using level_not E hU h

theorem gate_lift {U r v : ℕ} (hU : 1 ≤ U) (hr : r≤v) {P : X→Prop} (hf : gateP E U r P) :
    gateP E U v P := lift_level E hU hr hf

theorem gate_congr {U r : ℕ} {P Q : X→Prop} (h : gateP E U r P) (eqv : ∀ x, P x ↔ Q x) :
    gateP E U r Q := by have := funext (fun x => propext (eqv x)); rwa [← this]

theorem gate_card {J : Type} [Fintype J] {U r : ℕ} (hU : 4 ≤ U) (hl : Fintype.card J ≤ U)
    (P : J → X → Prop) [∀ j, DecidablePred (P j)] [∀ x, DecidablePred (fun i => P i x)]
    (h : ∀ j, gateP E U r (P j)) (a : ℕ) :
    gateP E U (r+4) (fun x => a ≤ (univ.filter (fun j => P j x)).card) := by
  classical
  let e := Fintype.equivFin J
  let fs := fun (i : Fin (Fintype.card J)) (x : X) => decide (P (e.symm i) x)
  have hf (i) : level E U r (fs i) := to_bool E (h (e.symm i)) (by intro x;simp [fs])
  have ht := level_threshold E hU hl fs hf a
  have eqv (x : X) : onCount fs x = (univ.filter (fun j => P j x)).card := by
    unfold onCount
    rw [e.symm.sum_comp (fun j => (decide (P j x)).toNat)] <;> try rfl
    have hz (j : J) : (decide (P j x)).toNat = if P j x then 1 else 0 := by by_cases hj : P j x <;> simp [hj]
    simp_rw [hz]
    exact sum_boole _ _
  apply of_bool E ht
  intro x; simp [eqv]

theorem gate_all {J : Type} [Fintype J] {U r : ℕ} (hU : 4 ≤ U) (hl : Fintype.card J ≤ U)
    (P : J → X → Prop) (h : ∀ j, gateP E U r (P j)) :
    gateP E U (r+4) (fun x => ∀ j, P j x) := by
  classical
  apply gate_congr E (gate_card E hU hl P h (Fintype.card J))
  intro x
  have hcap := card_filter_le univ (fun j => P j x)
  rw [card_univ] at hcap
  rw [show Fintype.card J = (univ : Finset J).card from rfl]
  rw [le_iff_eq_or_lt,eq_comm,card_filter_eq_iff]
  simp_all

theorem gate_and {U r : ℕ} (hU : 4 ≤ U) {P Q : X → Prop} (hP : gateP E U r P) (hQ : gateP E U r Q) :
    gateP E U (r+4) (fun x => P x ∧ Q x) := by
  let R := fun (b : Bool) => if b then P else Q
  have hr (b) : gateP E U r (R b) := by cases b <;> assumption
  apply gate_congr E (gate_all E hU (by simpa using (show 2≤U by omega)) R hr)
  intro x; simp [R,and_comm]

end SpinCircuit

namespace SpinCircuit
open Finset
abbrev Packet (d : ℕ) := Fin d → Option ℕ
def wireBit {W : ℕ} (v : Option ℕ) (j : Fin (W+1)) : Bool :=
  if j.val=0 then v.isSome else (v.getD 0).testBit (j.val-1)
def packetBits (d W : ℕ) (v : Packet d) := [false,true] ++ List.ofFn (fun i : Fin (d*(W+1)) =>
  let ij := finProdFinEquiv.symm i
  wireBit (v ij.1) ij.2)
def packet (d W : ℕ) : Encoding (Packet d) (2+d*(W+1)) where
  base := packetBits d W
  length v := by simp [packetBits];omega
  enough := by omega
  zero v := rfl
  one v := rfl

theorem packet_layout (d W : ℕ) (v : Packet d) : packetBits d W v = [false,true] ++
    (List.ofFn (fun i : Fin d => (v i).isSome :: List.ofFn (fun j : Fin W => ((v i).getD 0).testBit j.val))).flatten := by
  unfold packetBits
  rw [List.ofFn_mul]
  congr 2
  apply congrArg List.ofFn
  funext i
  have hh (j : Fin (W+1)) : (⟨i.val*(W+1)+j.val,by have hj:=j.isLt;have h:=Nat.mul_le_mul_right (W+1) i.isLt;rw [Nat.succ_mul] at h;omega⟩ : Fin (d*(W+1))) = finProdFinEquiv (i,j) := by
    apply Fin.ext; simp [Nat.add_comm,Nat.mul_comm]
  simp only [hh,Equiv.symm_apply_apply]
  rw [List.ofFn_succ]
  congr 1

theorem bit_gate {d W U r : ℕ} (i : Fin d) (j : Fin (W+1)) :
    level (packet d W) U r (fun y => wireBit (y i) j) := by
  let loc := finProdFinEquiv (i,j)
  let ix : Fin (2+d*(W+1)) := ⟨2+loc.val,by have h:=loc.isLt;omega⟩
  have h := read_input (packet d W).base (packet d W).length ix
  have hh (y : Packet d) : ((packet d W).base y).getD ix false = wireBit (y i) j := by
    change ([false,true] ++ _).getD (2+loc.val) false = _
    rw [Nat.add_comm 2]
    change (List.ofFn (fun u : Fin (d*(W+1)) => wireBit (y (finProdFinEquiv.symm u).1) (finProdFinEquiv.symm u).2)).getD loc.val false = _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos loc.isLt, Option.getD_some]
    exact congrArg (fun ij : Fin d × Fin (W+1) => wireBit (y ij.1) ij.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simpa only [level,hh] using weaken h (Nat.zero_le (U^r))

def clip (W : ℕ) (v : Option ℕ) := v.map (· % 2^W)
theorem bit_match (a v W : ℕ) (ha : a<2^W) :
    v%2^W = a ↔ ∀ j : Fin W, v.testBit j.val = a.testBit j.val := by
  have h : a%2^W = a := Nat.mod_eq_of_lt ha
  constructor
  · intro he j
    have hh := congrArg (fun z : ℕ => z.testBit j.val) he
    simpa [Nat.testBit_mod_two_pow,j.isLt] using hh
  · intro hb;rw [←h];apply Nat.eq_of_testBit_eq;intro j
    by_cases hj : j<W
    · simp [Nat.testBit_mod_two_pow,hj,hb ⟨j,hj⟩]
    · simp [Nat.testBit_mod_two_pow,hj]

theorem present_gate {d W U r : ℕ} (i : Fin d) :
    gateP (packet d W) U r (fun y => y i ≠ none) := by
  classical
  have h := bit_gate (W := W) (U := U) (r := r) i 0
  have hh (y : Packet d) : wireBit (y i) (0 : Fin (W+1)) = decide (y i ≠ none) := by
    cases hi : y i <;> simp [wireBit]
  apply of_bool (packet d W) h
  intro y;rw [hh];simp

theorem matches_constant {d W U : ℕ} (hU : 4≤U) (hW : W≤U) (i : Fin d) (a : ℕ) (ha : a<2^W) :
    gateP (packet d W) U 5 (fun y => (y i).getD 0 % 2^W = a) := by
  classical
  let P := fun (j : Fin W) (y : Packet d) => ((y i).getD 0).testBit j.val = a.testBit j.val
  have hp (j : Fin W) : gateP (packet d W) U 1 (P j) := by
    have hr := bit_gate (W:=W) (U:=U) (r:=0) i j.succ
    have hb (y : Packet d) : wireBit (y i) j.succ = ((y i).getD 0).testBit j.val := by simp [wireBit]
    simp only [hb] at hr
    cases hj : a.testBit j.val with
    | true =>
      have he (y : Packet d) : decide (P j y) = ((y i).getD 0).testBit j.val := by simp [P,hj]
      apply of_bool (packet d W) (lift_level (packet d W) (by omega : 1≤U) (by decide : 0≤1) hr)
      intro y;simp [P,hj]
    | false =>
      have he (y : Packet d) : decide (P j y) = !((y i).getD 0).testBit j.val := by simp [P,hj]
      apply of_bool (packet d W) (level_not (packet d W) hU hr)
      intro y;simp [P,hj]
  exact gate_congr (packet d W) (gate_all (packet d W) hU (by simpa using hW) P hp)
    (fun y => (bit_match a ((y i).getD 0) W ha).symm)

end SpinCircuit

namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k I d W U : ℕ}


theorem test_scaled (hU : 4≤U) (hW : W≤U) (i : Fin d) (k T : ℕ) :
    gateP (packet d W) U 5 (fun y => 4^k*((y i).getD 0 % 2^W)=T) := by
  classical
  by_cases h : ∃ a : ℕ, a<2^W ∧ 4^k*a=T
  · obtain ⟨a,ha,rfl⟩ := h
    exact gate_congr _ (matches_constant hU hW i a ha)
      (fun _ => (Nat.mul_right_inj (by positivity : (4:ℕ)^k ≠ 0)).symm)
  · apply gate_congr _ (gate_const (packet d W) U 5 False)
    intro y
    simp only [false_iff]
    intro hh
    exact h ⟨_,Nat.mod_lt _ (by positivity),hh⟩

theorem cost_bit (hU : 4≤U) (hW : W≤U) (i : Fin d) (k T : ℕ) :
    gateP (packet d W) U 10 (fun y =>
      ((clip W (y i)).map ((4:ℕ)^k*·)) ≠ none ∧ ((clip W (y i)).map ((4:ℕ)^k*·)) ≠ some T) := by
  apply gate_congr _ (gate_and _ hU (present_gate (d:=d) (W:=W) (U:=U) (r:=6) i)
    (gate_not _ hU (test_scaled hU hW i k T)))
  intro y;cases hi : y i <;> simp [clip]

theorem cost_cut (hU : 4≤U) (hW : W≤U) (hI : I≤U) (cards : Fin I → Fin d)
    (k : ℕ) (P : Fin I → ℕ) (j : ℕ) :
    gateP (packet d W) U 14 (fun y => j ≤ cost (fun i => (clip W (y (cards i))).map ((4:ℕ)^k*·)) P) := by
  classical
  apply gate_congr _ (gate_card _ hU (by simpa using hI)
    (fun i y => ((clip W (y (cards i))).map ((4:ℕ)^k*·)) ≠ none ∧
      ((clip W (y (cards i))).map ((4:ℕ)^k*·)) ≠ some (P i))
    (fun i => cost_bit hU hW (cards i) k (P i)) j)
  intro y
  unfold cost
  rw [Finset.sum_boole]
  rfl

theorem price_cut (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hM : Fintype.card (Model b k) ≤ U)
    (cards : Fin I → Fin d) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a j : ℕ) :
    gateP (packet d W) U 18 (fun y => j ≤ price k c m e a (fun i => clip W (y (cards i)))) := by
  classical
  let P := fun (M : Model b k) (y : Packet d) => j ≤ priced c m e a (fun i => clip W (y (cards i))) M
  have hp (M : Model b k) : gateP (packet d W) U 14 (P M) := by
    by_cases hh : ∃ q, project c (some e) = some q ∧ mult M q = a
    · apply gate_congr _ (cost_cut hU hW hI cards k (fun i => prediction c M (m i)) j)
      intro y;simp only [P,priced,if_pos hh]
    · apply gate_congr _ (gate_const (packet d W) U 14 (j≤I))
      intro y;simp only [P,priced,if_neg hh]
  apply gate_congr _ (gate_all _ hU hM P hp)
  intro y;simp [price,P,le_inf'_iff]

theorem card_lt (n z : ℕ) (h : z ≤ n) : (univ.filter (fun i : Fin n => i.val < z)).card = z := by
  by_cases hz : z<n
  · have hh : (univ.filter (fun i : Fin n => i.val < z)) = Finset.Iio (⟨z,hz⟩ : Fin n) := by ext i;simp; rfl
    rw [hh, Fin.card_Iio]
  · have he := Nat.le_antisymm h (by omega)
    subst z;simp

def rows {H I : ℕ} (W : ℕ) (y : Packet (H*I)) (h : Fin H) (i : Fin I) := clip W (y (finProdFinEquiv (h,i)))

theorem total_as_card {H : ℕ} (f : Fin H → Label t b) (m : Fin I → Mask b)
    (e : Pair t) (a : ℕ) (y : Fin H → Fin I → Option ℕ) :
    totalPrice k f m e a y = (univ.filter (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1))).card := by
  classical
  have h := Finset.sum_boole (R:=ℕ) (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1)) univ
  rw [Nat.cast_id, Fintype.sum_prod_type] at h
  rw [← h];unfold totalPrice
  apply sum_congr rfl;intro i _
  have hh := sum_boole (R:=ℕ) (fun u : Fin I => u.val < price k (f i) m e a (y i)) univ
  rw [Nat.cast_id,card_lt I _ (price_cap ..)] at hh
  exact hh.symm

theorem total_cut {H : ℕ} (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I≤U)
    (hM : Fintype.card (Model b k) ≤ U) (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a j : ℕ) :
    gateP (packet (H*I) W) U 22 (fun y => j ≤ totalPrice k f m e a (rows W y)) := by
  classical
  let P := fun (z : Fin H × Fin I) (y : Packet (H*I)) => z.2.val+1 ≤ price k (f z.1) m e a (rows W y z.1)
  have hp (z) : gateP (packet (H*I) W) U 18 (P z) := price_cut hU hW hI hM _ _ _ _ _ _
  apply gate_congr _ (gate_card _ hU (by simpa using hd) P hp j)
  intro y;rw [total_as_card]

theorem price_total_cap {H : ℕ} (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ)
    (y : Fin H → Fin I → Option ℕ) : totalPrice k f m e a y ≤ H*I := by
  rw [total_as_card]
  simpa using card_filter_le univ (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1))

end SpinCircuit

namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k H I W U : ℕ}
def winner (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a : Fin (k+1)) (y : Packet (H*I)) : Prop :=
  ∀ a' : Fin (k+1), totalPrice k f m e a.val (rows W y) ≤ totalPrice k f m e a'.val (rows W y)

theorem score_le_gate (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I+1≤U)
    (hM : Fintype.card (Model b k) ≤ U) (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a a' : ℕ) :
    gateP (packet (H*I) W) U 32 (fun y => totalPrice k f m e a (rows W y) ≤ totalPrice k f m e a' (rows W y)) := by
  let T := fun (a : ℕ) (y : Packet (H*I)) => totalPrice k f m e a (rows W y)
  let J := Fin (H*I+1)
  let good := fun (j : J) (y : Packet (H*I)) => ¬ (j.val ≤ T a y ∧ ¬ j.val ≤ T a' y)
  have cut (a j : ℕ) : gateP (packet (H*I) W) U 22 (fun y => j ≤ T a y) :=
    total_cut hU hW hI (by omega) hM f m e a j
  have hg (j : J) : gateP (packet (H*I) W) U 28 (good j) :=
    gate_not _ hU (gate_and _ hU (gate_lift _ (by omega : 1≤U) (by decide : 22≤23) (cut a j.val)) (gate_not _ hU (cut a' j.val)))
  apply gate_congr _ (gate_all _ hU (show Fintype.card J ≤ U by simpa [J] using hd) good hg)
  intro y
  change (∀ j : J, ¬ (j.val ≤ T a y ∧ ¬ j.val ≤ T a' y)) ↔ T a y ≤ T a' y
  constructor
  · intro hh
    have ht := price_total_cap (k:=k) f m e a (rows W y)
    let j : J := ⟨T a y,by dsimp [T];omega⟩
    have hj := hh j
    change ¬(T a y ≤ T a y ∧ ¬ T a y ≤ T a' y) at hj
    omega
  · intro h j;omega

theorem winner_gate (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I+1≤U)
    (hM : Fintype.card (Model b k) ≤ U) (hk : k+1≤U) (f : Fin H → Label t b)
    (m : Fin I → Mask b) (e : Pair t) (a : Fin (k+1)) :
    gateP (packet (H*I) W) U 36 (winner (W:=W) f m e a) := by
  exact gate_all _ hU (by simpa using hk) _ (fun a' : Fin (k+1) => score_le_gate hU hW hI hd hM f m e a.val a'.val)

theorem realizes {J : Type} [Fintype J] {X : Type} {n r : ℕ} (E : Encoding X n) (U : ℕ)
    (F : J → X → Bool) (hF : ∀ j, level E U r (F j)) (hj : Fintype.card J ≤ U) :
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (out : J → Fin (n+g.size)),
    g.size ≤ U^(r+1) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n g ∧
    (∀ gate ∈ g.gates, allowed gate) ∧ ∀ j x, (g.wires (E.base x)).getD (out j).val false = F j x := by
  classical
  let bij := Fintype.equivFin J
  let fs := fun (i : Fin (Fintype.card J)) => F (bij.symm i)
  obtain ⟨p,o,hp,hl,ho,he⟩ := indexed (B:=U^r) fs (fun i => hF (bij.symm i)) n le_rfl
  have hlegal := circuit_legal hp
  refine ⟨⟨p,0⟩,fun j => ⟨o (bij j),ho _⟩,?_,hlegal.1,hlegal.2,?_⟩
  · change p.length ≤ _
    rw [pow_succ,Nat.mul_comm (U^r)];exact hl.trans (Nat.mul_le_mul_right _ hj)
  · intro j x
    change (run p (E.base x)).getD (o (bij j)) false = F j x
    simpa [fs] using he x (E.base x) (E.length x) (by rfl) (bij j)
end SpinCircuit

namespace SpinHash
open SpinMass
def scale (t k s : ℕ) := (t+2)*(k+s+2)^(k+1)
def cap (t k s : ℕ) := (scale t k s)^32

theorem parameter_bounds (t k s : ℕ) (ht : 2 ≤ t) (hk : 0 < k) (hs : 3 ≤ s) :
    let U := cap t k s
    4  ≤  U ∧ k*(2*t+2)+1  ≤  U ∧ inner k s  ≤  U ∧ outer t k s * inner k s+1  ≤  U ∧
    Fintype.card (Model (colors k s) k)  ≤  U ∧ k+1  ≤  U ∧
    Fintype.card (Pair t × Fin (k+1))  ≤  U := by
  dsimp only
  let v := k+s+2
  let P := scale t k s
  have hv : 6 ≤ v := by dsimp [v];omega
  have hv1 : 1 ≤ v := by omega
  have hvk : v  ≤  v^(k+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hv1 (show 1 ≤ k+1 by omega)
  have hvs : v^(k+1)  ≤  P := by dsimp [P,scale];change v^_  ≤  (t+2)*v^_;nlinarith
  have hvt : t+2 ≤ P := by dsimp [P,scale];change t+2 ≤ (t+2)*v^_;nlinarith
  have hP := hvk.trans hvs
  have h4 : 6 ≤ P := hv.trans hP
  have hpow (a c : ℕ) (hac : a ≤ c) : P^a  ≤  P^c := Nat.pow_le_pow_right (by omega) hac
  have hp32 : P  ≤  P^32 := by simpa only [pow_one] using hpow 1 32 (by decide)
  have hu : k+1  ≤  P := by dsimp [v] at hP;omega
  have hss : s  ≤  P := by dsimp [v] at hP;omega
  have hprod : (k+1)*s  ≤  P^2 := by simpa [pow_two] using Nat.mul_le_mul hu hss
  have hlog : 1+Nat.log 2 ((k+1)*s)  ≤  P^3 := by
    have hh := (Nat.log_le_self 2 _).trans hprod
    nlinarith [Nat.mul_le_mul_left (P^2) h4]
  have hlogt : 1+Nat.log 2 t  ≤  P := by have := Nat.log_le_self 2 t;omega
  have hnum : 67584  ≤  P^7 := by
    exact (by decide : 67584  ≤  6^7).trans (Nat.pow_le_pow_left h4 7)
  have hd := (query_budget t k s (by omega)).trans
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hnum (Nat.pow_le_pow_left hu 2)) (Nat.pow_le_pow_left hss 3)) hlog) hlogt)
  have hds : outer t k s * inner k s  ≤  P^16 := hd.trans_eq (by ring)
  have hd' : outer t k s * inner k s + 1  ≤  P^32 := by
    have hx : P^16 < P^32 := Nat.pow_lt_pow_right (by omega) (by decide)
    omega
  have hout : 0 < outer t k s := by unfold outer colors outerL;positivity
  have hin : inner k s  ≤  outer t k s * inner k s := Nat.le_mul_of_pos_left _ hout
  have hW : k*(2*t+2)+1  ≤  P^3 := by
    have hx := Nat.mul_le_mul (show k ≤ P by omega) (show 2*t+2 ≤ 2*P by omega)
    nlinarith [Nat.mul_le_mul_left (P^2) h4]
  have hvCube : 128  ≤  v^3 := (by decide : 128 ≤ 6^3).trans (Nat.pow_le_pow_left hv 3)
  have hb : colors k s  ≤  v^5 := by
    have hk' : k+1 ≤ v := by dsimp [v];omega
    have hs' : s ≤ v := by dsimp [v];omega
    exact (Nat.mul_le_mul hvCube (Nat.mul_le_mul hk' hs')).trans_eq (by ring)
  have hcard (z : ℕ) : Fintype.card (Pair z)  ≤  z*z := by
    simpa using Fintype.card_le_of_injective (fun e : Pair z => e.val) Subtype.val_injective
  have hopt : Fintype.card (Option (Pair (colors k s)))  ≤  v^11 := by
    rw [Fintype.card_option]
    have h := (hcard _).trans (Nat.mul_le_mul hb hb)
    nlinarith [Nat.mul_le_mul_left (v^10) hv, Nat.one_le_pow 10 v (by omega)]
  have hmodel : Fintype.card (Model (colors k s) k)  ≤  P^11 := by
    change Fintype.card (Fin k → Option (Pair (colors k s)))  ≤  P^11
    simp only [Fintype.card_fun,Fintype.card_fin]
    calc
      _  ≤  (v^11)^k := Nat.pow_le_pow_left hopt k
      _  ≤  (v^(k+1))^11 := by rw [← pow_mul,← pow_mul];apply Nat.pow_le_pow_right hv1;omega
      _  ≤  _ := Nat.pow_le_pow_left hvs 11
  have hj : Fintype.card (Pair t × Fin (k+1))  ≤  P^3 := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact (Nat.mul_le_mul ((hcard t).trans (Nat.mul_le_mul (by omega : t ≤ P) (by omega : t ≤ P))) hu).trans_eq (by ring)
  exact ⟨by change 4 ≤ P^32;omega,hW.trans (hpow 3 32 (by decide)),by change _  ≤  P^32;omega,hd',
    hmodel.trans (hpow 11 32 (by decide)),hu.trans hp32,hj.trans (hpow 3 32 (by decide))⟩

theorem final_size (t k s : ℕ) : (cap t k s)^37 = (t+2)^1184*(k+s+2)^(1184*(k+1)) := by
  unfold cap scale
  rw [← pow_mul,mul_pow,← pow_mul,show 32*37=1184 by decide,Nat.mul_comm (k+1)]
end SpinHash

namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k H I : ℕ}
def batch (f : Fin H → Label t b) (m : Fin I → Mask b) (i : Fin (H*I)) : Mask t :=
  let z := finProdFinEquiv.symm i
  m z.2 ∘ f z.1

theorem flat_sum (F : Fin (H*I) → ℕ) : ∑ i, F i = ∑ h : Fin H, ∑ j : Fin I, F (finProdFinEquiv (h,j)) := by
  rw [← finProdFinEquiv.sum_comp F, Fintype.sum_prod_type]

def fullW (k t : ℕ) := k*(2*t+2)+1

theorem lost_rows (W : ℕ) (y : Packet (H*I)) :
    totalLost (rows W y) = (univ.filter (fun i => y i = none)).card := by
  have h := sum_boole (R:=ℕ) (fun i => y i=none) univ
  rw [Nat.cast_id,flat_sum] at h
  simpa [totalLost, rows, erasures,clip] using h

theorem error_rows (f : Fin H → Label t b) (m : Fin I → Mask b) (G : Model t k) (y : Packet (H*I)) :
    totalErrors f m G (rows (fullW k t) y) ≤ (univ.filter (fun i =>
      y i ≠ none ∧ y i ≠ some (reading G (batch f m i)))).card := by
  have h := sum_boole (R:=ℕ) (fun i => y i ≠ none ∧ y i ≠ some (reading G (batch f m i))) univ
  rw [Nat.cast_id,flat_sum] at h
  rw [←h];apply sum_le_sum;intro i _
  unfold cost
  apply sum_le_sum;intro j _
  let index := finProdFinEquiv (i,j)
  have hb : reading G (batch f m index) < 2^fullW k t := reading_bound _ _
  have hv : batch f m index = m j ∘ f i := by simp [batch,index]
  change (if clip (fullW k t) (y index) ≠ none ∧ clip (fullW k t) (y index) ≠ some (reading G (m j ∘ f i)) then 1 else 0) ≤
    if y index ≠ none ∧ y index ≠ some (reading G (batch f m index)) then 1 else 0
  rw [hv] at hb ⊢
  by_cases hl : y index = none
  · simp [hl,clip]
  · by_cases hh : y index = some (reading G (m j ∘ f i))
    · simp [hh,clip,Nat.mod_eq_of_lt hb]
    · simp [hl,hh];split <;> decide

theorem winning_value (f : Fin H → Label t b) (m : Fin I → Mask b) (G : Model t k) (e : Pair t)
    (W : ℕ) (y : Packet (H*I))
    (h : ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) (rows W y) < totalPrice k f m e a (rows W y))
    (a : Fin (k+1)) : winner (W:=W) f m e a y ↔ mult G e = a.val := by
  constructor
  · intro hw
    by_contra hn
    have hh := h a.val (fun hz => hn hz.symm)
    have hcap : mult G e ≤ k := by simpa [mult] using card_filter_le univ (fun l => G l=some e)
    have hle := hw ⟨mult G e,by omega⟩
    exact (not_lt_of_ge hle) hh
  · intro ha a'
    by_cases hn : a'.val = mult G e
    · rw [hn,ha]
    · exact ha ▸ (h a'.val hn).le
end SpinCircuit

end PEqualNP.Outside.L_pcx_469

open PEqualNP.Outside.L_pcx_469 PEqualNP.Outside.L_pcx_469.SpinCircuit PEqualNP.Outside.L_pcx_469.SpinHash PEqualNP.Outside.L_pcx_469.SpinMass Finset

theorem PEqualNP.Outside.L_pcx_469 : ∃ C A : ℕ, 0 < C ∧ ∀ t k s : ℕ, 2 ≤ t → 0 < k → 3 ≤ s →
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let E := Fin 3 × T
  let Mask := T → Fin 3
  let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
  let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
  let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs := fun (g : Option Pair) (p : Mask) =>
    ∑ x : V → Bool, if (∀ i : T, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2*t then
      ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0

  let Model := Fin k → Option Pair
  let read := fun (G : Model) (p : Mask) => ∏ l, obs (G l) p
  let W := k*(2*t+2)+1
  ∃ (d : ℕ) (batch : Fin d → Mask) (g : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Pair → Fin (k+1) → Fin (2+d*(W+1)+g.size)),
    0 < d ∧ d ≤ C*(k+1)^2*s^3*(1+Nat.log 2 ((k+1)*s))*(1+Nat.log 2 t) ∧
    g.size ≤ (t+2)^A*(k+s+2)^(A*(k+1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+d*(W+1)) g ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (G : Model), (∀ i, read G (batch i) < 2^W) ∧
      ∀ (y : Fin d → Option ℕ),
        let lost := (Finset.univ.filter (fun i => y i = none)).card
        let err := (Finset.univ.filter (fun i => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card
        9*s*(2*err+lost) < (4*s-9)*d →
        let bits := (List.ofFn (fun i : Fin d => (y i).isSome ::
          List.ofFn (fun j : Fin W => ((y i).getD 0).testBit j.val))).flatten
        ∀ (e : Pair) (m : Fin (k+1)), (g.wires ([false,true] ++ bits)).getD (out e m).val false =
          decide ((Finset.univ.filter (fun l => G l = some e)).card = m.val) := by
  classical
  refine ⟨67584,1184,by decide,?_⟩
  intro t k s ht hk hs
  dsimp only
  let H := outer t k s
  let I := inner k s
  let W := fullW k t
  let U := cap t k s
  obtain ⟨f,m,win⟩ := local_design t k s hs
  obtain ⟨hu,hw,hi,hd,hM,hk',hj⟩ := parameter_bounds t k s ht hk hs
  let Q := Pair t × Fin (k+1)
  let F := fun (z : Q) (y : Packet (H*I)) => decide (winner (W:=W) f m z.1 z.2 y)
  have hf (z : Q) : level (packet (H*I) W) U 36 (F z) := by
    apply to_bool (packet (H*I) W) (winner_gate hu hw hi hd hM hk' f m z.1 z.2)
    intro y; exact decide_eq_true_iff
  obtain ⟨g,o,hsize,hback,hops,heval⟩ := realizes (packet (H*I) W) U F hf hj
  have hH : 0 < H := by dsimp [H,outer,colors,outerL];positivity
  have hI : 0 < I := by dsimp [I,SpinHash.inner,slotBits];positivity
  refine ⟨H*I,batch f m,g,fun e a => o (e,a),Nat.mul_pos hH hI,query_budget t k s (by omega),?_,hback,hops,?_⟩
  · exact hsize.trans_eq (final_size ..)
  · intro G
    refine ⟨fun i => reading_bound G _,?_⟩
    intro y
    dsimp only
    intro hr e a
    have hbad := error_rows f m G y
    have hlost := lost_rows W y
    have hrob : 9*s*(2*totalErrors f m G (rows W y)+totalLost (rows W y)) < (4*s-9)*(H*I) := by
      apply lt_of_le_of_lt _ hr
      apply Nat.mul_le_mul_left
      rw [hlost]
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left 2 hbad
    have hwin := win G e (rows W y) hrob
    have hsem := heval (e,a) y
    change (g.wires ((packet (H*I) W).base y)).getD (o (e,a)).val false = decide (winner (W:=W) f m e a y) at hsem
    rw [show (packet (H*I) W).base y = _ from packet_layout _ _ y] at hsem
    change (g.wires _).getD (o (e,a)).val false = decide (mult G e = a.val)
    apply hsem.trans
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using winning_value f m G e W y hwin a

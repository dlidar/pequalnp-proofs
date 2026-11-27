import Mathlib

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

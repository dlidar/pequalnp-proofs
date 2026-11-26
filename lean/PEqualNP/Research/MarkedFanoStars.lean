import PEqualNP.Defs

namespace PEqualNP.Research.MarkedStars

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
abbrev F := DMFormula 14
abbrev V := Fin 14

def degree (i : V) : F → Nat
  | .lit v _ => if v = i then 1 else 0
  | .and a b => degree i a + degree i b
  | .or a b => max (degree i a) (degree i b)

def clean : F → Prop
  | .lit _ b => b = true
  | .and a b | .or a b => clean a ∧ clean b ∧ ¬ ∃ i, a = .lit i true ∧ b = .lit i true

def atoms : F → List V
  | .lit i _ => [i]
  | .and a b | .or a b => atoms a ++ atoms b

theorem length_atoms (f : F) : (atoms f).length = f.leaves := by
  induction f <;> simp_all [atoms,DMFormula.leaves]

theorem degree_le_count (i : V) (f : F) : degree i f ≤ (atoms f).count i := by
  induction f with
  | lit v b => by_cases h : v=i <;> simp [atoms,degree,h]
  | and a b ha hb => simp only [degree,atoms,List.count_append]; omega
  | or a b ha hb => simp only [degree,atoms,List.count_append]; omega

theorem eval_agree (f : F) (x y : V → Bool) (h : ∀ i ∈ atoms f, x i = y i) :
    f.eval x = f.eval y := by
  induction f with
  | lit i b => simp [DMFormula.eval,h i (by simp [atoms])]
  | and a b ha hb | or a b ha hb =>
    simp [DMFormula.eval,ha (fun i hi => h i (by simp [atoms,hi])),
      hb (fun i hi => h i (by simp [atoms,hi]))]

def pt (p : Fin 7) : V := ⟨p.val,by omega⟩
def ln (l : Fin 7) : V := ⟨7+l.val,by omega⟩
def star (p : Fin 7) (x : V → Bool) : Bool :=
  x (pt p) && decide (∃ l : Fin 7, p ∈ fanoLines l ∧ x (ln l) = true)
def nbr (p : Fin 7) : Finset V :=
  insert (pt p) ((Finset.univ.filter fun l : Fin 7 => p ∈ fanoLines l).image ln)

theorem four : ∀ p, (nbr p).card = 4 := by decide

theorem essential : ∀ p, ∀ i ∈ nbr p, ∃ j : V,
    star p (fun v => decide (v = j ∨ v = i)) ≠ star p (fun v => decide (v = j)) := by decide

theorem support (p : Fin 7) (f : F) (h : ∀ x, f.eval x = star p x) :
    nbr p ⊆ (atoms f).toFinset := by
  intro i hi
  obtain ⟨j,hj⟩ := essential p i hi
  by_contra e
  apply hj
  rw [← h, ← h]
  apply eval_agree
  intro v hv
  have ne : v ≠ i := fun eq => e (List.mem_toFinset.mpr (eq ▸ hv))
  simp [ne]

theorem excess (p : Fin 7) (f : F) (h : ∀ x, f.eval x = star p x)
    (i j : V) (ne : i ≠ j) :
    4 + (if 2 ≤ degree i f then 1 else 0) + (if 2 ≤ degree j f then 1 else 0) ≤ f.leaves := by
  let s := atoms f
  have inc := support p f h
  have base : 4 ≤ s.toFinset.card := (four p) ▸ Finset.card_le_card inc
  have ci := degree_le_count i f
  have cj := degree_le_count j f
  have erase_card (a : V) (t : List V) (hh : 2 ≤ t.count a) : (t.erase a).toFinset = t.toFinset := by
    ext v
    simp only [List.mem_toFinset, ← List.count_pos_iff]
    by_cases he : v = a
    · subst v; rw [List.count_erase_self]; omega
    · simp [List.count_erase_of_ne he]
  have len := length_atoms f
  change s.length = f.leaves at len
  change degree i f ≤ s.count i at ci
  change degree j f ≤ s.count j at cj
  split <;> split
  · rename_i hi hj
    have hi' : 2 ≤ s.count i := by omega
    have hj' : 2 ≤ (s.erase i).count j := by rw [List.count_erase_of_ne (Ne.symm ne)]; omega
    have b := List.toFinset_card_le ((s.erase i).erase j)
    rw [erase_card _ _ hj',erase_card _ _ hi'] at b
    have l1 := List.length_erase_of_mem (List.count_pos_iff.mp (by omega : 0 < s.count i))
    have l2 := List.length_erase_of_mem (List.count_pos_iff.mp (by omega : 0 < (s.erase i).count j))
    omega
  · have hd : 2 ≤ s.count i := by omega
    have b := List.toFinset_card_le (s.erase i)
    rw [erase_card _ _ hd] at b
    have := List.length_erase_of_mem (List.count_pos_iff.mp (by omega : 0 < s.count i))
    omega
  · have hd : 2 ≤ s.count j := by omega
    have b := List.toFinset_card_le (s.erase j)
    rw [erase_card _ _ hd] at b
    have := List.length_erase_of_mem (List.count_pos_iff.mp (by omega : 0 < s.count j))
    omega
  · have := List.toFinset_card_le s; omega

def join (g : Fin 7 → F) : F := DMFormula.or (g 0) (DMFormula.or (g 1) (DMFormula.or (g 2) (DMFormula.or (g 3) (DMFormula.or (g 4) (DMFormula.or (g 5) (g 6))))))

theorem join_size (g : Fin 7 → F) : (join g).leaves = ∑ p, (g p).leaves := by
  simp [join, DMFormula.leaves, Fin.sum_univ_succ]

theorem join_marks (g : Fin 7 → F) (i : V) :
    2 ≤ degree i (join g) → ∃ p, 2 ≤ degree i (g p) := by
  simp only [join,degree,le_max_iff]
  rintro (h|h|h|h|h|h|h)
  all_goals exact ⟨_,h⟩

theorem joint_lower (g : Fin 7 → F) (hg : ∀ p x, (g p).eval x = star p x)
    (i j : V) (hn : i ≠ j) (hi : 2 ≤ degree i (join g)) (hj : 2 ≤ degree j (join g)) :
    30 ≤ (join g).leaves := by
  classical
  have hit (k : V) (h : 2 ≤ degree k (join g)) :
      1 ≤ ∑ p : Fin 7, (if 2 ≤ degree k (g p) then 1 else 0 : Nat) := by
    obtain ⟨p,hp⟩ := join_marks g k h
    have hh := Finset.single_le_sum (f := fun a : Fin 7 => if 2 ≤ degree k (g a) then (1 : Nat) else 0)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ p)
    simpa [hp] using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun p _ => excess p (g p) (hg p) i j hn)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  rw [join_size]
  have := hit i hi
  have := hit j hj
  omega

def off (p : Fin 7) (k : ℕ) : Fin 7 := ⟨(p.val + 7 - k) % 7, Nat.mod_lt _ (by decide)⟩
theorem incid : ∀ p l, p ∈ fanoLines l ↔ l = off p 0 ∨ l = off p 1 ∨ l = off p 3 := by decide
def raw (v : V) : F := .lit v true
def arm (p : Fin 7) : F := .and (raw (pt p))
  (.or (raw (ln (off p 0))) (.or (raw (ln (off p 1))) (raw (ln (off p 3)))))

theorem arm_eval (p : Fin 7) (x : V → Bool) : (arm p).eval x = star p x := by
  simp [arm,raw,DMFormula.eval,star,incid,or_and_right,exists_or]

def arms (a b p : Fin 7) : F :=
  if a = p then .and (arm p) (.or (raw (pt p)) (raw (ln b))) else arm p

theorem arms_eval (a b p : Fin 7) (x : V → Bool) : (arms a b p).eval x = star p x := by
  by_cases he : a=p
  · simp only [arms,if_pos he,DMFormula.eval,raw,arm_eval]
    unfold star
    cases x (pt p) <;> simp
  · simp [arms,he,arm_eval]

def isRaw (f : F) : Option V := match f with | .lit i true => some i | _ => none
def ok : F → Bool
  | .lit _ b => b
  | .and a b | .or a b => ok a && ok b && !(isRaw a != none && isRaw a == isRaw b)

theorem ok_clean (f : F) (h : ok f = true) : clean f := by
  induction f with
  | lit i b => exact h
  | and a b ha hb | or a b ha hb =>
    simp only [ok,Bool.and_eq_true] at h
    refine ⟨ha h.1.1,hb h.1.2,?_⟩
    rintro ⟨i,rfl,rfl⟩
    simp [isRaw] at h

set_option maxRecDepth 5000 in
theorem checked_arms : ∀ a b : Fin 7, a ∈ fanoLines b →
    let f := join (arms a b)
    ok f = true ∧ f.leaves = 30 ∧ 2 ≤ degree (pt a) f ∧ 2 ≤ degree (ln b) f := by decide


theorem join_eval (g : Fin 7 → F) (x : V → Bool) :
    (join g).eval x = true ↔ ∃ p, (g p).eval x = true := by
  simp [join,DMFormula.eval,Fin.exists_fin_succ]

open PEqualNP.GenericRejection

theorem star_circuit (C : Circuit) (hc : ComputesIncidence fanoLines C) (x : V → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ p, star p x = true := by
  let X := Finset.univ.filter (fun p => x (pt p) = true)
  let Y := Finset.univ.filter (fun l => x (ln l) = true)
  have h : incidenceInput X Y = List.ofFn x := by
    rw [List.ofFn_add (n := 7) (m := 7)]
    have hp (i) : decide (i ∈ X) = x (pt i) := by apply Bool.eq_iff_iff.mpr; simp [X]
    have hl (i) : decide (i ∈ Y) = x (ln i) := by apply Bool.eq_iff_iff.mpr; simp [Y]
    simp only [incidenceInput,hp,hl]
    rfl
  rw [← h,hc]
  simp [incidenceFun,X,Y,star,and_comm]

theorem joint_upper (C : Circuit) (hc : ComputesIncidence fanoLines C) (a b : Fin 7) (hab : a ∈ fanoLines b) :
    ∃ f : F, clean f ∧ f.leaves = 30 ∧ (∀ x, f.eval x = C.eval (List.ofFn x)) ∧
       2 ≤ degree (pt a) f ∧ 2 ≤ degree (ln b) f := by
  obtain ⟨hok,hs,hp,hl⟩ := checked_arms a b hab
  refine ⟨join (arms a b),ok_clean _ hok,hs,?_,hp,hl⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [join_eval,star_circuit C hc]
  simp only [arms_eval]

end PEqualNP.Research.MarkedStars

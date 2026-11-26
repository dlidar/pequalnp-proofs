import Mathlib.Tactic
import Mathlib.Combinatorics.SetFamily.LYM
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# One-way cut widths of the order-four incidence plane with one flag removed

The bit at index m in the packed table records whether a union of point
neighborhoods equals the 21-bit line mask m. A new point either leaves the
old mask in place or sets its incident line bits. The kernel checks the resulting
counts with natural-number bitwise operations. Singleton line queries
distinguish any two different unions. Monotone decoding constrains their
message order, and a monotone encoder imposes a further diagonal matching bound.

These are communication bounds across the point/line partition. Gate sharing
and the total size of an arbitrary circuit are outside these bounds.
-/
namespace PEqualNP.Research.PuncturedPlaneCut
open Finset

set_option exponentiation.threshold 3000000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Position m stores whether the 21-bit neighborhood m can occur. This mask
selects positions whose j-th index bit is zero, in a table with 2^k positions. -/
def stripes : Nat → Nat → Nat
  | 0, _ => 1
  | k+1, j => if k=j then 2^(2^k)-1 else
      let z := stripes k j
      z ||| (z <<< (2^k))

theorem stripes_bit {k j} (h : j<k) (m : Nat) :
    (stripes k j).testBit m = (decide (m<2^k) && !(m.testBit j)) := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
    by_cases eq : k=j
    · subst j
      simp only [stripes]
      by_cases low : m<2^k
      · have up : m<2^(k+1) := by rw [pow_succ]; omega
        simp [low,up,Nat.testBit_lt_two_pow low]
      · by_cases up : m<2^(k+1)
        · simp [low,up,Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega : 2^k≤m) up]
        · simp [low,up]
    · have jk : j<k := by omega
      simp only [stripes,eq,ite_false,Nat.testBit_or,Nat.testBit_shiftLeft,ih jk]
      by_cases low : m<2^k
      · have up : m<2^(k+1) := by rw [pow_succ]; omega
        simp [low,up,show ¬m≥2^k by omega]
      · have ge : m≥2^k := by omega
        have sum : 2^k+(m-2^k)=m := by omega
        have bit := Nat.testBit_two_pow_add_gt jk (m-2^k)
        rw [sum] at bit
        have cut : m-2^k<2^k ↔ m<2^(k+1) := by rw [pow_succ]; omega
        simp [low,ge,cut,←bit]

def force (s j : Nat) := let lo := stripes 21 j
  (s ^^^ (s &&& lo)) ||| ((s &&& lo) <<< (2^j))

def put (j z : Nat) := if z.testBit j then z else z+2^j

private theorem or_add {u v : Nat} (h : u &&& v = 0) : u ||| v = u+v := by
  induction v using Nat.div2Induction generalizing u with
  | ind v ih =>
    rcases Nat.eq_zero_or_pos v with rfl|hv
    · simp
    have half : (u/2) &&& (v/2) = 0 := by rw [← Nat.and_div_two,h]
    have halves := ih hv half
    have bottom : ¬ (u%2=1 ∧ v%2=1) := by
      intro hb; have := Nat.and_mod_two_eq_one.mpr hb; rw [h] at this; contradiction
    have comp := Nat.mod_add_div (u ||| v) 2
    rw [Nat.or_mod_two,Nat.or_div_two,halves] at comp
    rcases Nat.mod_two_eq_zero_or_one u with hl|hl <;>
      rcases Nat.mod_two_eq_zero_or_one v with hr|hr <;> simp [hl,hr] at bottom comp <;> omega

theorem put_or (j z : Nat) : put j z = z ||| 2^j := by
  cases b : z.testBit j with
  | false =>
    simp only [put,b]
    apply Eq.symm
    apply or_add
    simp [Nat.and_two_pow,b]
  | true =>
    simp only [put,b,ite_true]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : j=i
    · subst i; simp [b]
    · simp [Nat.testBit_two_pow_of_ne hi]

theorem force_bit {j m} (hj : j<21) (hm : m<2^21) (s : Nat) :
    (force s j).testBit m = true ↔ ∃ z<2^21, s.testBit z = true ∧ put j z = m := by
  have small : m-2^j < 2^21 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm
  simp only [force,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_shiftLeft,
    stripes_bit hj,hm,small,decide_true,Bool.true_and]
  constructor
  · intro h
    by_cases sm : s.testBit m = true ∧ m.testBit j = true
    · exact ⟨m,hm,sm.1,by simp [put,sm.2]⟩
    · have rest : m≥2^j ∧ s.testBit (m-2^j) = true ∧ (m-2^j).testBit j = false := by
        revert h sm
        cases s.testBit m <;> cases m.testBit j <;> cases s.testBit (m-2^j) <;>
          cases (m-2^j).testBit j <;> simp
      exact ⟨m-2^j,small,rest.2.1,by simp [put,rest.2.2]; omega⟩
  · rintro ⟨z,hz,hit,eq⟩
    cases b : z.testBit j with
    | true => simp [put,b] at eq; subst m; simp [b,hit]
    | false =>
      simp [put,b] at eq
      subst m
      simp [hit,b]

def rows (p : Nat) := (if p=0 then [5,7,17,20] else [0,5,7,17,20]).map fun d => (p+d)%21
def joinRow (p z : Nat) := (rows p).foldl (fun x j => put j x) z
def unions : Nat → Nat
  | 0 => 1
  | n+1 => let v := unions n; v ||| (rows n).foldl force v

private theorem fold_force (js : List Nat) (valid : ∀ j∈js, j<21) (s m : Nat) (hm : m<2^21) :
    (js.foldl force s).testBit m = true ↔
    ∃ z<2^21, s.testBit z = true ∧ js.foldl (fun x j => put j x) z = m := by
  induction js generalizing s with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨fun h => ⟨m,hm,h,rfl⟩,fun ⟨z,_,h,e⟩ => e ▸ h⟩
  | cons j tail ih =>
    have hj := valid j (by simp)
    have ht : ∀ i∈tail, i<21 := fun i hi => valid i (by simp [hi])
    simp only [List.foldl_cons,ih ht]
    constructor
    · rintro ⟨v,hv,h,eq⟩
      obtain ⟨z,hz,hits,hput⟩ := (force_bit hj hv s).mp h
      exact ⟨z,hz,hits,by rwa [hput]⟩
    · rintro ⟨z,hz,hits,eq⟩
      have bound : put j z<2^21 := by
        rw [put_or]; exact Nat.or_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) hj)
      exact ⟨_,bound,(force_bit hj bound s).mpr ⟨z,hz,hits,rfl⟩,eq⟩

def neighborhood (onPts : Nat → Bool) : Nat → Nat
  | 0 => 0
  | p+1 => let m := neighborhood onPts p; if onPts p then joinRow p m else m

theorem neighborhood_bound (x : Nat → Bool) (r : Nat) : neighborhood x r < 2^21 := by
  induction r with
  | zero => exact (by decide : 0 < 2^21)
  | succ r ih =>
    simp only [neighborhood]; split
    · unfold joinRow
      apply List.foldlRecOn (motive:=fun (z : Nat) => z<2^21)
      · exact ih
      · intro z hz j hj
        rw [put_or]; exact Nat.or_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) (by
          obtain ⟨u,_,rfl⟩ := List.mem_map.mp hj; exact Nat.mod_lt _ (by decide)))
    · exact ih

theorem row_range {m} (hm : m<2^21) (n : Nat) :
    (unions n).testBit m = true ↔ ∃ x, neighborhood x n = m := by
  induction n generalizing m with
  | zero =>
    simp only [unions,neighborhood,Nat.testBit_one_eq_true_iff_self_eq_zero,exists_const]
    exact eq_comm
  | succ n ih =>
    have good (j) (hj : j ∈ rows n) : j < 21 := by
      obtain ⟨d,_,rfl⟩ := List.mem_map.mp hj
      exact Nat.mod_lt _ (by decide)
    simp only [unions,Nat.testBit_or,Bool.or_eq_true,fold_force _ good _ _ hm,ih hm]
    have agree (x y : Nat → Bool) (r : Nat) (h : ∀ i<r, x i=y i) :
        neighborhood x r = neighborhood y r := by
      induction r with
      | zero => rfl
      | succ r ih =>
        simp only [neighborhood,h r (by omega),ih (fun i hi => h i (by omega))]
    constructor
    · rintro (⟨x,hx⟩|⟨z,hz,hits,hrow⟩)
      · use Function.update x n false
        simp [neighborhood,←hx,agree (Function.update x n false) x n
          (fun i hi => Function.update_of_ne (by omega) _ _)]
      · obtain ⟨x,hx⟩ := (ih hz).mp hits
        use Function.update x n true
        simp [neighborhood,agree (Function.update x n true) x n
          (fun i hi => Function.update_of_ne (by omega) _ _),hx,joinRow,hrow]
    · rintro ⟨x,hx⟩
      cases on : x n
      · exact Or.inl ⟨x,by simpa [neighborhood,on] using hx⟩
      · exact Or.inr ⟨_,neighborhood_bound x n,(ih (neighborhood_bound x n)).mpr ⟨x,rfl⟩,by simpa [neighborhood,on,joinRow] using hx⟩

/-- Split the table into two equal contiguous blocks; empty blocks cost one test. -/
def cnt (d x : Nat) : Nat :=
  match d with
  | 0 => x%2
  | n+1 => if x=0 then 0 else cnt n (x % 2^(2^n)) + cnt n (x >>> (2^n))

theorem cnt_spec (d x : Nat) :
    cnt d x = ∑ i ∈ range (2^d), (x.testBit i).toNat := by
  induction d generalizing x with
  | zero =>
    simp only [cnt,pow_zero,sum_range_one,Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h|h <;> simp [h]
  | succ n ih =>
    rw [cnt]
    split
    · rename_i h; simp [h]
    · rw [show 2^(n+1)=2^n+2^n by rw [pow_succ]; omega,Finset.sum_range_add,ih,ih]
      congr 1
      · apply sum_congr rfl; intro i hi
        simp [Nat.testBit_mod_two_pow,mem_range.mp hi]
      · simp [Nat.testBit_shiftRight]

def keys := (Finset.range (2^21)).filter fun m => (unions 21).testBit m = true

theorem key_count : keys.card = 24925 := by
  have number : cnt 21 (unions 21) = 24925 := by decide +kernel
  rw [cnt_spec] at number
  unfold keys
  rw [Finset.card_filter]
  convert number using 1
  apply sum_congr rfl; intro i hi
  cases (unions 21).testBit i <;> rfl

private theorem fold_bits (js : List Nat) (z l : Nat) :
    (js.foldl (fun x j => put j x) z).testBit l = (z.testBit l || decide (l ∈ js)) := by
  induction js generalizing z with
  | nil => simp
  | cons j js ih =>
    rw [List.foldl_cons,ih,put_or,Nat.testBit_or,Nat.testBit_two_pow]
    simp only [List.mem_cons]
    by_cases h : j=l
    · subst j; simp
    · simp [h,Ne.symm h]

theorem neighborhood_bit (x : Nat → Bool) (n l : Nat) :
    (neighborhood x n).testBit l = true ↔ ∃ p<n, x p = true ∧ l ∈ rows p := by
  induction n with
  | zero => simp [neighborhood]
  | succ n ih =>
    rw [Nat.exists_lt_succ_right]
    cases on : x n <;> simp [neighborhood,on,joinRow,fold_bits,ih,or_comm]


/-- The exact Boolean expression in L-meta-9769. -/
def posted (x : Fin 42 → Bool) :=
  (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)

private def listed : List (Fin 21 × Fin 21) :=
  [(0,5), (0,7), (0,17), (0,20), (1,0), (1,1), (1,6), (1,8), (1,18), (2,1), (2,2), (2,7), (2,9), (2,19), (3,2), (3,3), (3,8), (3,10), (3,20), (4,0), (4,3), (4,4), (4,9), (4,11), (5,1), (5,4), (5,5), (5,10), (5,12), (6,2), (6,5), (6,6), (6,11), (6,13), (7,3), (7,6), (7,7), (7,12), (7,14), (8,4), (8,7), (8,8), (8,13), (8,15), (9,5), (9,8), (9,9), (9,14), (9,16), (10,6), (10,9), (10,10), (10,15), (10,17), (11,7), (11,10), (11,11), (11,16), (11,18), (12,8), (12,11), (12,12), (12,17), (12,19), (13,9), (13,12), (13,13), (13,18), (13,20), (14,0), (14,10), (14,13), (14,14), (14,19), (15,1), (15,11), (15,14), (15,15), (15,20), (16,0), (16,2), (16,12), (16,15), (16,16), (17,1), (17,3), (17,13), (17,16), (17,17), (18,2), (18,4), (18,14), (18,17), (18,18), (19,3), (19,5), (19,15), (19,18), (19,19), (20,4), (20,6), (20,16), (20,19), (20,20)]

private theorem listed_rows : ∀ p l : Fin 21,
    (p,l) ∈ listed ↔ l.val ∈ rows p.val := by decide +kernel

private theorem posted_list (x : Fin 42 → Bool) : posted x =
    listed.any (fun e => x (Fin.castAdd 21 e.1) && x (Fin.natAdd 21 e.2)) := by
  simp only [posted,listed,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  rfl

/-- Keep the first n points and set each hidden line to false. -/
def input (n : Nat) (hidden : List Nat) (x y : Nat → Bool) : Fin 42 → Bool :=
  Fin.addCases (m:=21) (n:=21) (fun p => decide (p.val<n) && x p.val)
    (fun l => decide (l.val ∉ hidden) && y l.val)

theorem posted_restricted {n} (hn : n≤21) (hidden : List Nat) (x y : Nat → Bool) :
    posted (input n hidden x y) = true ↔ ∃ l<21, l ∉ hidden ∧
      (neighborhood x n).testBit l = true ∧ y l = true := by
  rw [posted_list,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,edge,hit⟩
    simp only [input,Fin.addCases_left,Fin.addCases_right,Bool.and_eq_true,decide_eq_true_eq] at hit
    exact ⟨l,l.isLt,hit.2.1,(neighborhood_bit _ _ _).mpr ⟨p,hit.1.1,hit.1.2,(listed_rows p l).mp edge⟩,hit.2.2⟩
  · rintro ⟨l,hl,vis,hbit,hy⟩
    obtain ⟨p,hp,hx,edge⟩ := (neighborhood_bit _ _ _).mp hbit
    let p' : Fin 21 := ⟨p,by omega⟩
    let l' : Fin 21 := ⟨l,hl⟩
    refine ⟨(p',l'),(listed_rows p' l').mpr edge,?_⟩
    simp only [input,Fin.addCases_left,Fin.addCases_right,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨hp,hx⟩,vis,hy⟩

def visible (n : Nat) (hidden : List Nat) (x : Nat → Bool) :=
  hidden.foldl (fun z j => put j z) (neighborhood x n)

theorem visible_bound (n : Nat) (hidden : List Nat) (hv : ∀ j∈hidden, j<21) (x : Nat → Bool) :
    visible n hidden x < 2^21 := by
  apply List.foldlRecOn (motive:=fun z : Nat => z<2^21)
  · exact neighborhood_bound x n
  · intro z hz j hj
    rw [put_or]; exact Nat.or_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) (hv j hj))

def messages (n : Nat) (hidden : List Nat) :=
  (range (2^21)).filter fun m => (hidden.foldl force (unions n)).testBit m = true

theorem mem_messages {n m} (hidden : List Nat) (hv : ∀ j∈hidden, j<21) :
    m ∈ messages n hidden ↔ ∃ x, visible n hidden x = m := by
  simp only [messages,mem_filter,mem_range]
  constructor
  · rintro ⟨hm,hits⟩
    obtain ⟨z,hz,hs,eq⟩ := (fold_force _ hv _ _ hm).mp hits
    obtain ⟨x,hx⟩ := (row_range hz n).mp hs
    exact ⟨x,by simpa [visible,hx] using eq⟩
  · rintro ⟨x,rfl⟩
    have bound := visible_bound n hidden hv x
    exact ⟨bound,(fold_force _ hv _ _ bound).mpr ⟨_,neighborhood_bound _ _,
      (row_range (neighborhood_bound x n) n).mpr ⟨x,rfl⟩,rfl⟩⟩

theorem messages_card (n : Nat) (hidden : List Nat) :
    (messages n hidden).card = cnt 21 (hidden.foldl force (unions n)) := by
  rw [messages,Finset.card_filter,cnt_spec]
  apply sum_congr rfl; intro i hi
  cases (hidden.foldl force (unions n)).testBit i <;> rfl

private theorem visible_bit (n : Nat) (hidden : List Nat) (x : Nat → Bool) (l : Nat) :
    (visible n hidden x).testBit l = ((neighborhood x n).testBit l || decide (l ∈ hidden)) :=
  fold_bits _ _ _

theorem indistinguishable {n} (hn : n≤21) (hidden : List Nat) (hv : ∀ j∈hidden, j<21)
    (x z : Nat → Bool) :
    (∀ y, posted (input n hidden x y) = posted (input n hidden z y)) ↔
    visible n hidden x = visible n hidden z := by
  have singleton (u : Nat → Bool) (l : Nat) (hl : l<21) (showLine : l∉hidden) :
      posted (input n hidden u (fun j => decide (j=l))) = (neighborhood u n).testBit l := by
    apply Bool.eq_iff_iff.mpr
    simp [posted_restricted hn,hl,showLine]
  constructor
  · intro same
    apply Nat.eq_of_testBit_eq
    intro l
    by_cases hl : l<21
    · by_cases hh : l ∈ hidden
      · simp [visible_bit,hh]
      · have eq := same (fun j => decide (j=l))
        rwa [singleton _ _ hl hh,singleton _ _ hl hh,← show (visible n hidden x).testBit l =
          (neighborhood x n).testBit l by simp [visible_bit,hh],
          ← show (visible n hidden z).testBit l = (neighborhood z n).testBit l by simp [visible_bit,hh]] at eq
    · have cut : 2^21 ≤ 2^l := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (visible_bound _ _ hv x) cut),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (visible_bound _ _ hv z) cut)]
  · intro eq y
    apply Bool.eq_iff_iff.mpr
    rw [posted_restricted hn,posted_restricted hn]
    have bits (l : Nat) (hh : l∉hidden) :
        (neighborhood x n).testBit l = (neighborhood z n).testBit l := by
      have h := congrArg (fun m : Nat => m.testBit l) eq
      simpa [visible_bit,hh] using h
    constructor <;> rintro ⟨l,hl,hh,hb,hy⟩
    · exact ⟨l,hl,hh,(bits l hh) ▸ hb,hy⟩
    · exact ⟨l,hl,hh,(bits l hh).symm ▸ hb,hy⟩

noncomputable def representative {n hidden} (hv : ∀ j∈hidden, j<21)
    (m : ↥(messages n hidden)) := Classical.choose ((mem_messages hidden hv).mp m.property)

theorem representative_eq {n hidden} (hv : ∀ j∈hidden, j<21) (m : ↥(messages n hidden)) :
    visible n hidden (representative hv m) = m.val :=
  Classical.choose_spec ((mem_messages hidden hv).mp m.property)

theorem binary_width {n b} (hn : n≤21) (hidden : List Nat) (hv : ∀ j∈hidden, j<21) :
    (∃ (enc : (Nat → Bool) → (Fin b → Bool)) (dec : (Fin b → Bool) → (Nat → Bool) → Bool),
      ∀ x y, posted (input n hidden x y) = dec (enc x) y) ↔ (messages n hidden).card ≤ 2^b := by
  classical
  constructor
  · rintro ⟨enc,dec,ok⟩
    have inj : Function.Injective (fun m : ↥(messages n hidden) => enc (representative hv m)) := by
      intro a b h
      apply Subtype.ext
      rw [← representative_eq hv a, ← representative_eq hv b]
      apply (indistinguishable hn hidden hv _ _).mp
      intro y
      rw [ok,ok]; exact congrArg (fun m => dec m y) h
    simpa using Fintype.card_le_of_injective _ inj
  · intro h
    have hc : Fintype.card ↥(messages n hidden) ≤ Fintype.card (Fin b → Bool) := by simpa using h
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
    let msg (x : Nat → Bool) : ↥(messages n hidden) :=
      ⟨visible n hidden x,(mem_messages _ hv).mpr ⟨x,rfl⟩⟩
    let recover (m : Fin b → Bool) (y : Nat → Bool) := if hm : ∃ a, e a = m then
      posted (input n hidden (representative hv (Classical.choose hm)) y) else false
    refine ⟨fun x => e (msg x),recover,?_⟩
    intro x y
    have hm : ∃ a, e a = e (msg x) := ⟨_,rfl⟩
    simp only [recover,dite_eq_left hm]
    rw [e.injective (Classical.choose_spec hm)]
    exact (indistinguishable hn hidden hv x _).mpr (representative_eq hv (msg x)).symm y

theorem full_count : (messages 21 []).card = 24925 := key_count
theorem delete_point_count : (messages 20 []).card = 20268 := by rw [messages_card]; decide +kernel
/-- These inputs distinguish every incident point from the collective input
containing all the points off the tested line. -/
def one (p : Fin 21) (i : Nat) := decide (i=p.val)
def off (l : Fin 21) (i : Nat) := decide (l.val ∉ rows i)

private theorem probe (x : Nat → Bool) (l : Fin 21) :
    posted (input 21 [] x (one l)) = true ↔ ∃ p<21, x p = true ∧ l.val ∈ rows p := by
  rw [posted_restricted (by decide : 21≤21),← neighborhood_bit]
  simp [one,l.isLt]

theorem incident_probe (p l : Fin 21) :
    posted (input 21 [] (one p) (one l)) = true ↔ l.val ∈ rows p.val := by
  rw [probe]; simp [one,p.isLt]

theorem off_probe (l : Fin 21) : posted (input 21 [] (off l) (one l)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨p,_,hp,hl⟩ := (probe _ _).mp h
  exact (of_decide_eq_true hp) hl

private theorem one_le_off {p l : Fin 21} (h : l.val ∉ rows p.val) : one p ≤ off l := by
  intro i
  by_cases hi : i=p.val <;> simp [one,off,hi,h]

private def mate (p : Fin 21) : Fin 21 := p + 5

private theorem matching_geometry :
    (∀ p : Fin 21, (mate p).val ∈ rows p.val) ∧
    ∀ p q : Fin 21, p ≠ q → ¬((mate p).val ∈ rows q.val ∧ (mate q).val ∈ rows p.val) := by decide +kernel

/-- If both sides of a point-to-line cut compute monotone functions, no
compression below the original 21 signals is possible. The assigned graph's
shift-by-five incidences form a fooling set for monotone messages. -/
theorem monotone_width {b} (enc : (Nat → Bool) → (Fin b → Bool))
    (dec : (Fin b → Bool) → (Nat → Bool) → Bool)
    (correct : ∀ x y, posted (input 21 [] x y) = dec (enc x) y)
    (me : Monotone enc) (md : ∀ y, Monotone (fun m => dec m y)) : 21 ≤ b := by
  have separate (p : Fin 21) : ¬ enc (one p) ≤ enc (off (mate p)) := by
    intro le
    have w := md (one (mate p)) le
    change dec (enc (one p)) (one (mate p)) ≤ dec (enc (off (mate p))) (one (mate p)) at w
    rw [← correct,← correct,(incident_probe p (mate p)).mpr (matching_geometry.1 p),off_probe] at w
    exact (by decide : ¬true ≤ false) w
  have witness (p : Fin 21) : ∃ j, enc (one p) j = true ∧ enc (off (mate p)) j = false := by
    by_contra! no
    apply separate p
    intro j
    cases h : enc (one p) j
    · simp
    · have hb : enc (off (mate p)) j = true := by simpa using no j h
      rw [hb]
  choose j high low using witness
  have sound (p l : Fin 21) (h : j p=j l) : (mate l).val ∈ rows p.val := by
    by_contra miss
    have w := me (one_le_off miss) (j l)
    rw [← h,high,h,low] at w
    exact (by decide : ¬true ≤ false) w
  have inj : Function.Injective j := by
    intro p l same
    by_contra ne
    exact matching_geometry.2 p l ne ⟨sound l p same.symm,sound p l same⟩
  simpa using Fintype.card_le_of_injective _ inj

theorem monotone_width_attained :
    ∃ (enc : (Nat → Bool) → (Fin 21 → Bool)) (dec : (Fin 21 → Bool) → (Nat → Bool) → Bool),
      (∀ x y, posted (input 21 [] x y) = dec (enc x) y) ∧
      Monotone enc ∧ ∀ y, Monotone (fun m => dec m y) := by
  let dec (m : Fin 21 → Bool) (y : Nat → Bool) :=
    decide (∃ p l : Fin 21, m p = true ∧ l.val ∈ rows p.val ∧ y l.val = true)
  refine ⟨fun x p => x p.val,dec,?_,fun _ _ h p => h p.val,?_⟩
  · intro x y
    apply Bool.eq_iff_iff.mpr
    simp only [posted_restricted (by decide : 21≤21),List.mem_nil_iff,not_false_eq_true,true_and,dec,decide_eq_true_eq,neighborhood_bit]
    constructor
    · rintro ⟨l,hl,⟨p,hp,hx,edge⟩,hy⟩
      exact ⟨⟨p,hp⟩,⟨l,hl⟩,hx,edge,hy⟩
    · rintro ⟨p,l,hx,edge,hy⟩
      exact ⟨_,l.isLt,⟨_,p.isLt,hx,edge⟩,hy⟩
  · intro y m m' le
    apply Bool.le_iff_imp.mpr
    simp only [dec,decide_eq_true_eq]
    rintro ⟨p,l,hp,edge,hy⟩
    exact ⟨p,l,Bool.le_iff_imp.mp (le p) hp,edge,hy⟩


theorem delete_incident_count : (messages 20 [20]).card = 15517 := by rw [messages_card]; decide +kernel
theorem delete_nonincident_count : (messages 20 [0]).card = 16870 := by rw [messages_card]; decide +kernel

def layer : Nat → Nat → Nat
  | 0,r => if r=0 then 1 else 0
  | _+1,0 => 1
  | k+1,r+1 => layer k (r+1) ||| ((layer k r) <<< (2^k))

def ones (k m : Nat) := (range k).filter (fun i => m.testBit i = true)

private theorem weight_zero {m k} (hm : m<2^k) : (ones k m).card=0 ↔ m=0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have empty := Finset.card_eq_zero.mp h
    by_cases hi : i<k
    · by_contra ne
      have hb : m.testBit i = true := by simpa using ne
      have : i ∈ ones k m := mem_filter.mpr ⟨mem_range.mpr hi,hb⟩
      simp [empty] at this
    · have hi' : k ≤ i := by omega
      have hbi := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi'))
      simpa using hbi
  · rintro rfl; simp [ones]

theorem layer_bit (k r m : Nat) : (layer k r).testBit m = true ↔ m<2^k ∧ (ones k m).card=r := by
  induction k generalizing r m with
  | zero =>
    cases r <;> simp [ones,layer,Nat.testBit_one_eq_true_iff_self_eq_zero]
  | succ k ih =>
    cases r with
    | zero =>
      simp only [layer,Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · rintro rfl; simp [ones]
      · exact fun ⟨hm,h⟩ => (weight_zero hm).mp h
    | succ r =>
      simp only [layer,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ih]
      by_cases low : m<2^k
      · have up : m<2^(k+1) := by rw [pow_succ]; omega
        have stable : ones (k+1) m = ones k m := by
          simp [ones,range_add_one,Finset.filter_insert,Nat.testBit_lt_two_pow low]
        simp [low,show ¬m≥2^k by omega,up,stable]
      · have ge : 2^k≤m := by omega
        by_cases up : m<2^(k+1)
        · have b := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt ge up
          have sm : m-2^k < 2^k := by rw [pow_succ] at up; omega
          have same : ones k m = ones k (m-2^k) := by
            apply Finset.ext
            intro i
            simp only [ones,mem_filter,mem_range]
            by_cases hi : i<k
            · have e := Nat.testBit_two_pow_add_gt hi (m-2^k)
              rw [show 2^k+(m-2^k)=m by omega] at e
              simp [hi,e]
            · simp [hi]
          have oneMore : (ones (k+1) m).card = (ones k m).card + 1 := by
            simp [ones,range_add_one,Finset.filter_insert,b,Finset.card_insert_of_notMem]
          simp [low,ge,up,sm,oneMore,same]
        · have big : ¬m-2^k<2^k := by rw [pow_succ] at up; omega
          simp [low,ge,up,big]


def middle := (messages 21 []).filter fun m => (ones 21 m).card = 16

theorem middle_count : middle.card = 9448 := by
  have num : cnt 21 (unions 21 &&& layer 21 16) = 9448 := by decide +kernel
  rw [cnt_spec] at num
  have same : middle = (range (2^21)).filter (fun m => (unions 21 &&& layer 21 16).testBit m = true) := by
    apply Finset.ext; intro m
    rw [middle,Finset.mem_filter,messages,Finset.mem_filter,Finset.mem_filter]
    simp only [List.foldl_nil,Finset.mem_range,Nat.testBit_and,Bool.and_eq_true,layer_bit]
    exact ⟨fun ⟨⟨hm,hu⟩,hw⟩ => ⟨hm,hu,hm,hw⟩,fun ⟨hm,hu,_,hw⟩ => ⟨⟨hm,hu⟩,hw⟩⟩
  rw [same,Finset.card_filter]
  convert num using 1
  apply sum_congr rfl; intro i hi
  cases (unions 21 &&& layer 21 16).testBit i <;> rfl

private noncomputable def fullRep (a : ↥middle) : Nat → Bool :=
  representative (n:=21) (hidden:=[]) (by simp) ⟨a.val,(mem_filter.mp a.property).1⟩

private theorem fullRep_key (a : ↥middle) : neighborhood (fullRep a) 21 = a.val :=
  representative_eq (n:=21) (hidden:=[]) (by simp) ⟨a.val,(mem_filter.mp a.property).1⟩

/-- A decoder monotone in the received bits must assign incomparable codewords to
the 9448 different neighborhoods of size 16. The encoder may be arbitrary. -/
theorem monotone_decoder_bound {b} (enc : (Nat → Bool) → (Fin b → Bool))
    (dec : (Fin b → Bool) → (Nat → Bool) → Bool)
    (ok : ∀ x y, posted (input 21 [] x y) = dec (enc x) y)
    (md : ∀ y, Monotone (fun m => dec m y)) :
    9448 ≤ b.choose (b/2) := by
  classical
  let code (a : ↥middle) := univ.filter fun j => enc (fullRep a) j = true
  have order (a z : ↥middle) (sub : code a ⊆ code z) : a=z := by
    have le : enc (fullRep a) ≤ enc (fullRep z) := by
      intro j; apply Bool.le_iff_imp.mpr; intro on
      exact (mem_filter.mp (sub (mem_filter.mpr ⟨mem_univ _,on⟩))).2
    have test (m : ↥middle) (l : Fin 21) :
        posted (input 21 [] (fullRep m) (one l)) = true ↔ m.val.testBit l.val = true := by
      rw [probe,←neighborhood_bit,fullRep_key]
    have hits : ones 21 a.val ⊆ ones 21 z.val := by
      intro i hi
      obtain ⟨lt,bit⟩ := mem_filter.mp hi
      let l : Fin 21 := ⟨i,mem_range.mp lt⟩
      have h := md (one l) le
      change dec (enc (fullRep a)) (one l) ≤ dec (enc (fullRep z)) (one l) at h
      rw [←ok,←ok] at h
      exact mem_filter.mpr ⟨lt,(test z l).mp (Bool.le_iff_imp.mp h ((test a l).mpr bit))⟩
    have eq := Finset.eq_of_subset_of_card_le hits
      (by rw [(mem_filter.mp z.property).2,(mem_filter.mp a.property).2])
    apply Subtype.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i<21
    · apply Bool.eq_iff_iff.mpr
      have e := Finset.ext_iff.mp eq i
      simpa [ones,hi] using e
    · have bound (v : ↥middle) : v.val<2^i := lt_of_lt_of_le
        (fullRep_key v ▸ neighborhood_bound (fullRep v) 21) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow (bound a),Nat.testBit_lt_two_pow (bound z)]
  let fam := univ.image code
  have anti : IsAntichain (· ⊆ ·) (fam : Set (Finset (Fin b))) := by
    intro A hA Z hZ ne sub
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hZ
    exact ne (congrArg code (order a z sub))
  have count : fam.card = middle.card := by
    have inj : Function.Injective code := fun a z h => order a z h.subset
    simp [fam,Finset.card_image_of_injective _ inj]
  have bound := anti.sperner
  simpa [count,middle_count] using bound

theorem monotone_decoder_width {b} (enc : (Nat → Bool) → (Fin b → Bool))
    (dec : (Fin b → Bool) → (Nat → Bool) → Bool)
    (ok : ∀ x y, posted (input 21 [] x y) = dec (enc x) y)
    (md : ∀ y, Monotone (fun m => dec m y)) : 16 ≤ b := by
  by_contra! small
  have h := monotone_decoder_bound enc dec ok md
  have bad : ∀ j : Fin 16, j.val.choose (j.val/2) < 9448 := by decide +kernel
  exact (Nat.not_lt_of_ge h) (bad ⟨b,small⟩)



/-- Exact neighborhood counts after hiding one additional line. -/
theorem single_line_profile_21 (l : Fin 21) : (messages 21 [l.val]).card = ([20406, 20268, 20268, 20268, 20268, 19874, 20268, 19874, 20268, 20268, 20268, 20268, 20268, 20268, 20268, 20268, 20268, 19874, 20268, 20268, 19874] : List Nat)[l.val]! := by
  rw [messages_card]
  fin_cases l <;> decide +kernel

/-- Exact neighborhood counts after hiding one additional line. -/
theorem single_line_profile_20 (l : Fin 21) : (messages 20 [l.val]).card = ([16870, 16824, 16824, 16824, 16013, 16576, 16013, 16576, 16824, 16824, 16824, 16824, 16824, 16824, 16824, 16824, 16013, 16576, 16824, 16013, 15517] : List Nat)[l.val]! := by
  rw [messages_card]
  fin_cases l <;> decide +kernel

end PEqualNP.Research.PuncturedPlaneCut

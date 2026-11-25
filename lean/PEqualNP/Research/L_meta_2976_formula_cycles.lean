import Mathlib.Tactic
import PEqualNP.Defs.DeMorganFormula

/-!
# Induced paths and bipartite incidence formulas

Restrict the two interior vertices of an induced path independently and let both
outer vertices have one common value. The resulting truth table is majority of
three bits. A finite closure calculation shows that the two interior vertices
cannot produce this table with only two literal occurrences in total, even when
the outer variables can be repeated freely.

In a four-cycle-free bipartite graph with no isolated vertices, a matching of
interior edges therefore gives one additional literal per matched edge above
the number of vertices. For disjoint cycles of length at least six this is
sharp, and every minimum formula has a fixed multiplicity on each side of each
cycle. The size measure here is the leaf count of a De Morgan formula.
-/

namespace PEqualNP.Research.PathFormulaCharge
open PEqualNP.MetaComplexity Finset
abbrev Byte := BitVec 8

/-- The low four bits and high four bits are the two outside assignments.
Within each block the two distinguished inputs have masks 10 and 12. -/
private def pool : Nat → List Byte
  | 0 => [0, 15, 240, 255]
  | 1 => [0, 3, 5, 10, 12, 15, 48, 51, 63, 80, 85, 95, 160, 170, 175, 192, 204, 207, 240, 243, 245, 250, 252, 255]
  | 2 => [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 31, 32, 34, 35, 42, 47, 48, 49, 50, 51, 53, 55, 58, 59, 60, 63, 64, 68, 69, 76, 79, 80, 81, 83, 84, 85, 87, 90, 92, 93, 95, 112, 115, 117, 119, 127, 128, 136, 138, 140, 143, 160, 162, 163, 165, 168, 170, 171, 172, 174, 175, 176, 179, 186, 187, 191, 192, 195, 196, 197, 200, 202, 204, 205, 206, 207, 208, 213, 220, 221, 223, 224, 234, 236, 238, 239, 240, 241, 242, 243, 244, 245, 247, 248, 250, 251, 252, 253, 254, 255]
  | _ => []

private def admissible (k : Nat) (z : Byte) : Prop := 3 ≤ k ∨ z ∈ pool k

private theorem combine (a b : Nat) (u v : Byte) (hu : admissible a u) (hv : admissible b v) :
    admissible (a+b) (u &&& v) ∧ admissible (a+b) (u ||| v) := by
  by_cases h : 3 ≤ a+b
  · exact ⟨Or.inl h,Or.inl h⟩
  have tab : ∀ i j : Fin 3, ∀ x ∈ pool i.val, ∀ y ∈ pool j.val,
      3 ≤ i.val+j.val ∨ ((x &&& y) ∈ pool (i.val+j.val) ∧ (x ||| y) ∈ pool (i.val+j.val)) := by decide +kernel
  have ha : ¬3 ≤ a := by omega
  have hb : ¬3 ≤ b := by omega
  obtain ⟨hx,hy⟩ := (tab ⟨a,by omega⟩ ⟨b,by omega⟩ u (hu.resolve_left ha) v (hv.resolve_left hb)).resolve_left h
  exact ⟨Or.inr hx,Or.inr hy⟩

def weight {n} (charge : Fin n → Nat) : DMFormula n → Nat
  | .lit i _ => charge i
  | .and a b | .or a b => weight charge a + weight charge b

def trace {n} (v : Fin n → Byte) : DMFormula n → Byte
  | .lit i b => if b then v i else ~~~(v i)
  | .and a b => trace v a &&& trace v b
  | .or a b => trace v a ||| trace v b

theorem trace_eval {n} (f : DMFormula n) (v : Fin n → Byte) (k : Fin 8) :
    (trace v f).getLsbD k.val = f.eval (fun i => (v i).getLsbD k.val) := by
  induction f with
  | lit i b => cases b <;> simp [trace,DMFormula.eval,k.isLt]
  | and a b ha hb => simp only [trace,DMFormula.eval,BitVec.getLsbD_and,ha,hb]
  | or a b ha hb => simp only [trace,DMFormula.eval,BitVec.getLsbD_or,ha,hb]

private theorem accounting {n} (f : DMFormula n) (cost : Fin n → Nat) (v : Fin n → Byte)
    (h : ∀ i, admissible (cost i) (v i) ∧ admissible (cost i) (~~~(v i))) :
    admissible (weight cost f) (trace v f) := by
  induction f with
  | lit i b => cases b <;> simp [weight,trace,h]
  | and a b ha hb => exact (combine _ _ _ _ ha hb).1
  | or a b ha hb => exact (combine _ _ _ _ ha hb).2

def table {n} (u v : Fin n) (context : Fin n → Bool) (i : Fin n) : Byte :=
  if i=u then 170 else if i=v then 204 else if context i then 240 else 0

def fee {n} (u v i : Fin n) : Nat := if i=u ∨ i=v then 1 else 0

/-- Switching the two-variable cofactor from AND to OR costs at least three occurrences
of the two variables, even with arbitrary repetitions elsewhere and negated literals. -/
theorem switching_cost {n} (f : DMFormula n) (u v : Fin n) (ctx : Fin n → Bool)
    (sw : trace (table u v ctx) f = 232) : 3 ≤ weight (fee u v) f := by
  have h := accounting f (fee u v) (table u v ctx) (by
    intro i
    have ok : ∀ (z : Byte), z ∈ ([170,204] : List Byte) →
        admissible 1 z ∧ admissible 1 (~~~z) := by unfold admissible; decide +kernel
    have other : ∀ (z : Byte), z ∈ ([0,240] : List Byte) →
        admissible 0 z ∧ admissible 0 (~~~z) := by unfold admissible; decide +kernel
    by_cases hu : i=u
    · simpa [fee,table,hu] using ok 170 (by decide)
    · by_cases hv : i=v
      · subst i
        simpa [fee,table,hu] using ok 204 (by decide)
      · cases hc : ctx i
        · simpa [fee,table,hu,hv,hc] using other 0 (by decide)
        · simpa [fee,table,hu,hv,hc] using other 240 (by decide))
  rw [sw] at h
  rcases h with h|h
  · exact h
  · by_contra! small
    have ht : ∀ i : Fin 3, (232 : Byte) ∉ pool i.val := by decide +kernel
    exact ht ⟨_,small⟩ h

theorem packed_weight {n t} (f : DMFormula n) (a b : Fin t → Fin n)
    (hd : ∀ i, ∑ k, fee (a k) (b k) i ≤ 1) :
    ∑ k, weight (fee (a k) (b k)) f ≤ f.leaves := by
  induction f with
  | lit i s => exact hd i
  | and u v h g | or u v h g =>
    simp only [weight, DMFormula.leaves,Finset.sum_add_distrib]
    omega

theorem packed_switches {n t} (f : DMFormula n) (a b : Fin t → Fin n)
    (ctx : Fin t → Fin n → Bool) (hd : ∀ i, ∑ k, fee (a k) (b k) i ≤ 1)
    (hs : ∀ k, trace (table (a k) (b k) (ctx k)) f = 232) : 3*t ≤ f.leaves := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t))) (fun k _ => switching_cost f _ _ _ (hs k))
  have hp := packed_weight f a b hd
  simp at h
  omega

def represents {n m} (E : Fin n → Fin m → Prop) [DecidableRel E] (f : DMFormula (n+m)) :=
  ∀ x, f.eval x = decide (∃ p l, E p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)

private theorem apart {n m} (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have e := congrArg Fin.val h
  change p.val = n+l.val at e
  omega

private theorem apart' {n m} (l : Fin m) (p : Fin n) : Fin.natAdd n l ≠ Fin.castAdd m p := (apart p l).symm

@[simp] private theorem right_inj {n m} (a b : Fin m) : Fin.natAdd n a = Fin.natAdd n b ↔ a=b := by simp [Fin.ext_iff]

def outsidePair {n m} (c : Fin n) (d : Fin m) (i : Fin (n+m)) :=
  decide (i = Fin.castAdd m c ∨ i = Fin.natAdd n d)

/-- The central incidence (a,b) of an induced path c-b-a-d switches
from AND to OR when both endpoints are turned on. -/
theorem path_switch {n m} (E : Fin n → Fin m → Prop) [DecidableRel E]
    (f : DMFormula (n+m)) (hf : represents E f) (a c : Fin n) (b d : Fin m)
    (ac : a ≠ c) (bd : b ≠ d) (ab : E a b) (ad : E a d) (cb : E c b) (cd : ¬ E c d) :
    trace (table (Fin.castAdd m a) (Fin.natAdd n b) (outsidePair c d)) f = 232 := by
  let V := table (Fin.castAdd m a) (Fin.natAdd n b) (outsidePair c d)
  have left (i : Fin n) : V (Fin.castAdd m i) = (if i=a then 170 else if i=c then 240 else 0) := by
    by_cases ia : i=a <;> by_cases ic : i=c <;> simp [V,table,outsidePair,ia,ic,apart]
  have right (j : Fin m) : V (Fin.natAdd n j) = (if j=b then 204 else if j=d then 240 else 0) := by
    simp only [V,table,outsidePair,apart',right_inj,false_or,ite_false,decide_eq_true_eq]
  change trace V f = 232
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let k : Fin 8 := ⟨t,ht⟩
  change (trace V f).getLsbD k.val = _
  rw [trace_eval,hf]
  have rect : (∃ i j, E i j ∧ (V (Fin.castAdd m i)).getLsbD k.val = true ∧
      (V (Fin.natAdd n j)).getLsbD k.val = true) ↔
      (((170 : Byte).getLsbD k.val = true ∧ (204 : Byte).getLsbD k.val = true) ∨
       ((170 : Byte).getLsbD k.val = true ∧ (240 : Byte).getLsbD k.val = true) ∨
       ((240 : Byte).getLsbD k.val = true ∧ (204 : Byte).getLsbD k.val = true)) := by
    constructor
    · rintro ⟨i,j,he,hi,hj⟩
      rw [left] at hi
      rw [right] at hj
      split at hi <;> split at hj
      all_goals repeat first | split at hi | split at hj
      all_goals simp_all
    · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩|⟨h₁,h₂⟩)
      · exact ⟨a,b,ab,by simpa [left] using h₁,by simpa [right] using h₂⟩
      · exact ⟨a,d,ad,by simpa [left] using h₁,by simpa [right,bd.symm] using h₂⟩
      · exact ⟨c,b,cb,by simpa [left,ac.symm] using h₁,by simpa [right] using h₂⟩
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply rect.trans
  exact (by decide +kernel : ∀ k : Fin 8,
    (((170 : Byte).getLsbD k.val = true ∧ (204 : Byte).getLsbD k.val = true) ∨
      ((170 : Byte).getLsbD k.val = true ∧ (240 : Byte).getLsbD k.val = true) ∨
      ((240 : Byte).getLsbD k.val = true ∧ (204 : Byte).getLsbD k.val = true)) ↔
      (232 : Byte).getLsbD k.val = true) k


/-- A pair of perfect matchings whose alternating cycles have length at least six. -/
def cycleEdges {n} (q : Equiv.Perm (Fin n)) (p l : Fin n) : Prop := l = p ∨ l = q p
instance {n} (q : Equiv.Perm (Fin n)) : DecidableRel (cycleEdges q) := by
  unfold cycleEdges; infer_instance

theorem cycles_lower {n} (q : Equiv.Perm (Fin n)) (long : ∀ i, q (q i) ≠ i)
    (f : DMFormula (n+n)) (h : represents (cycleEdges q) f) : 3*n ≤ f.leaves := by
  have free (i : Fin n) : q i ≠ i := by
    intro he; exact long i (by simp [he])
  apply packed_switches f (Fin.castAdd n) (Fin.natAdd n) (fun i => outsidePair (q.symm i) (q i))
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [fee,apart,Fin.castAdd_inj,or_false]
      simp
    | right i =>
      simp only [fee,apart',right_inj,false_or]
      simp
  · intro i
    apply path_switch _ _ h
    · intro he
      exact free i ((congrArg q he).trans (q.apply_symm_apply i))
    · exact (free i).symm
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr (q.apply_symm_apply i).symm
    · rintro (he|he)
      · exact long i ((congrArg q he).trans (q.apply_symm_apply i))
      · exact free i (he.trans (q.apply_symm_apply i))

private def row {n} (q : Equiv.Perm (Fin n)) (i : Fin n) : DMFormula (n+n) :=
  .and (.lit (Fin.castAdd n i) true) (.or (.lit (Fin.natAdd n i) true) (.lit (Fin.natAdd n (q i)) true))

private theorem fold_rows {n} (q : Equiv.Perm (Fin n)) (rs : List (Fin n)) (a : DMFormula (n+n)) :
    (rs.foldl (fun g i => g.or (row q i)) a).leaves = a.leaves + 3*rs.length ∧
    ∀ x, (rs.foldl (fun g i => g.or (row q i)) a).eval x = true ↔
      a.eval x = true ∨ ∃ i ∈ rs, (row q i).eval x = true := by
  induction rs generalizing a with
  | nil => simp
  | cons i rs ih =>
    rw [List.foldl_cons]
    constructor
    · rw [(ih _).1]; simp [row,DMFormula.leaves]; omega
    · intro x
      rw [(ih _).2]
      simp only [DMFormula.eval,Bool.or_eq_true,List.mem_cons]
      aesop

theorem cycles_upper {n} (hn : 0 < n) (q : Equiv.Perm (Fin n)) :
    ∃ f : DMFormula (n+n), f.leaves = 3*n ∧ represents (cycleEdges q) f := by
  cases e : List.finRange n with
  | nil => have h := congrArg List.length e; simp at h; omega
  | cons a rs =>
    refine ⟨rs.foldl (fun g i => g.or (row q i)) (row q a), ?_, ?_⟩
    · rw [(fold_rows q rs _).1]
      have h := congrArg List.length e
      simp [row,DMFormula.leaves] at *
      omega
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [(fold_rows q rs _).2]
      simp only [decide_eq_true_eq]
      have allmem (i : Fin n) : i=a ∨ i ∈ rs := by
        have h := List.mem_finRange i
        rwa [e,List.mem_cons] at h
      have desc (i : Fin n) : (row q i).eval x = true ↔
          ∃ l, cycleEdges q i l ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n l) = true := by
        simp [row,DMFormula.eval,cycleEdges]
        aesop
      constructor
      · rintro (h|⟨i,_,h⟩)
        · exact ⟨a,(desc a).mp h⟩
        · exact ⟨i,(desc i).mp h⟩
      · rintro ⟨i,l,hl⟩
        have h := (desc i).mpr ⟨l,hl⟩
        rcases allmem i with rfl|hm
        · exact Or.inl h
        · exact Or.inr ⟨i,hm,h⟩

/-- The number of occurrences counts literals of either sign. -/
def uses {n} (f : DMFormula n) (i : Fin n) := weight (fun j => if i=j then 1 else 0) f

private theorem no_occurrence {n} (f : DMFormula n) (i : Fin n) (h : uses f i = 0)
    (x y : Fin n → Bool) (same : ∀ j, j ≠ i → x j = y j) : f.eval x = f.eval y := by
  induction f with
  | lit j s =>
    have neq : j ≠ i := by rintro rfl; simp [uses,weight] at h
    simp only [DMFormula.eval, same j neq]
  | and a b ha hb | or a b ha hb =>
    simp only [uses,weight,Nat.add_eq_zero_iff] at h
    simp [DMFormula.eval, ha h.1,hb h.2]

theorem essential_occurs {n} (f : DMFormula n) (i : Fin n) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j) (diff : f.eval x ≠ f.eval y) : 1 ≤ uses f i := by
  by_contra! small
  exact diff (no_occurrence f i (by omega) x y same)

private theorem total_uses {n} (f : DMFormula n) : ∑ i, uses f i = f.leaves := by
  induction f with
  | lit j s => simp [uses, weight, DMFormula.leaves]
  | and a b ha hb | or a b ha hb =>
    simp only [uses,weight,DMFormula.leaves,Finset.sum_add_distrib] at *
    omega

private theorem pair_uses {n} (f : DMFormula n) (u v : Fin n) (ne : u ≠ v) :
    weight (fee u v) f = uses f u + uses f v := by
  induction f with
  | lit i s =>
    by_cases hu : i=u <;> by_cases hv : i=v <;> simp_all [weight,fee,uses,eq_comm]
  | and a b ha hb | or a b ha hb =>
    simp only [weight,uses] at *; omega

/-- Each disjoint switching pair contributes one extra occurrence beyond the
one needed at every essential input. Vertices outside the matching still count. -/
theorem partial_matching_lower {n t} (f : DMFormula n) (a b : Fin t → Fin n)
    (separate : ∀ k, a k ≠ b k) (ctx : Fin t → Fin n → Bool)
    (disjoint : ∀ j, ∑ k, fee (a k) (b k) j ≤ 1)
    (essential : ∀ j, 1 ≤ uses f j)
    (hs : ∀ k, trace (table (a k) (b k) (ctx k)) f = 232) : n+t ≤ f.leaves := by
  let surplus (j : Fin n) := uses f j - 1
  have splitAt (j : Fin n) : uses f j = 1 + surplus j := by
    have := essential j; dsimp [surplus]; omega
  have hit (k : Fin t) : 1 ≤ surplus (a k) + surplus (b k) := by
    have h := switching_cost f _ _ _ (hs k)
    rw [pair_uses _ _ _ (separate k),splitAt (a k),splitAt (b k)] at h
    omega
  have expand (k : Fin t) : ∑ j, fee (a k) (b k) j * surplus j =
      surplus (a k) + surplus (b k) := by
    have eqn (j : Fin n) : fee (a k) (b k) j * surplus j =
        (if j=a k then surplus j else 0) + (if j=b k then surplus j else 0) := by
      have ne := (separate k).symm
      by_cases ha : j=a k <;> by_cases hb : j=b k <;> simp_all [fee]
    simp only [eqn, Finset.sum_add_distrib]
    simp
  have cap (j : Fin n) : ∑ k, fee (a k) (b k) j * surplus j ≤ surplus j := by
    rw [← Finset.sum_mul]
    simpa using Nat.mul_le_mul_right (surplus j) (disjoint j)
  have charged : t ≤ ∑ j, surplus j := calc
    _ = ∑ _k : Fin t, 1 := by simp
    _ ≤ ∑ k, (surplus (a k) + surplus (b k)) := Finset.sum_le_sum fun k _ => hit k
    _ = ∑ j, ∑ k, fee (a k) (b k) j * surplus j := by simp_rw [← expand]; rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum fun j _ => cap j
  have total := total_uses f
  simp_rw [splitAt,Finset.sum_add_distrib] at total
  simp at total
  omega

/-- For a graph with no isolated vertices, all raw inputs are essential. -/
theorem incident_occurs {n m} (E : Fin n → Fin m → Prop) [DecidableRel E]
    (f : DMFormula (n+m)) (hf : represents E f)
    (rows : ∀ p, ∃ l, E p l) (cols : ∀ l, ∃ p, E p l) (i : Fin (n+m)) :
    1 ≤ uses f i := by
  induction i using Fin.addCases with
  | left p =>
    obtain ⟨l, edge⟩ := rows p
    let x := outsidePair p l
    let y := fun j : Fin (n+m) => decide (j = Fin.natAdd n l)
    apply essential_occurs f _ x y
    · intro j ne; simp [x,y,outsidePair,ne]
    · have yes : f.eval x = true := by
        rw [hf, decide_eq_true_eq]
        exact ⟨p,l,edge,by simp [x,outsidePair],by simp [x,outsidePair]⟩
      rw [yes,hf]; simp [y,apart]
  | right l =>
    obtain ⟨p, edge⟩ := cols l
    let x := outsidePair p l
    let y := fun j : Fin (n+m) => decide (j = Fin.castAdd m p)
    apply essential_occurs f _ x y
    · intro j ne; simp [x,y,outsidePair,ne]
    · have yes : f.eval x = true := by
        rw [hf, decide_eq_true_eq]
        exact ⟨p,l,edge,by simp [x,outsidePair],by simp [x,outsidePair]⟩
      rw [yes,hf]; simp [y,apart']

/-- In a square-free bipartite graph without isolates, any matching of edges whose
endpoints have degree at least two charges one extra literal per matched edge. -/
theorem bipartite_matching_lower {n m t} (E : Fin n → Fin m → Prop) [DecidableRel E]
    (f : DMFormula (n+m)) (hf : represents E f)
    (thin : ∀ a c b d, a ≠ c → b ≠ d → E a b → E a d → E c b → ¬ E c d)
    (rows : ∀ p, ∃ l, E p l) (cols : ∀ l, ∃ p, E p l)
    (a : Fin t ↪ Fin n) (b : Fin t ↪ Fin m) (edges : ∀ i, E (a i) (b i))
    (sideA : ∀ i, ∃ d, b i ≠ d ∧ E (a i) d)
    (sideB : ∀ i, ∃ c, a i ≠ c ∧ E c (b i)) : n+m+t ≤ f.leaves := by
  classical
  choose d hd had using sideA
  choose c hc hcb using sideB
  apply partial_matching_lower f (fun k => Fin.castAdd m (a k)) (fun k => Fin.natAdd n (b k))
    (fun k => apart (a k) (b k)) (fun k => outsidePair (c k) (d k))
  · intro i
    induction i using Fin.addCases with
    | left p =>
      simp only [fee,Fin.castAdd_inj,apart,or_false]
      by_cases h : ∃ k, p=a k
      · obtain ⟨k,rfl⟩ := h
        simp
      · simp [not_exists.mp h]
    | right l =>
      simp only [fee,right_inj,apart',false_or]
      by_cases h : ∃ k, l=b k
      · obtain ⟨k,rfl⟩ := h
        simp
      · simp [not_exists.mp h]
  · exact incident_occurs E f hf rows cols
  · intro k
    exact path_switch E f hf _ _ _ _ (hc k) (hd k) (edges k) (had k) (hcb k)
      (thin _ _ _ _ (hc k) (hd k) (edges k) (had k) (hcb k))

theorem path_occurrences {n m} (E : Fin n → Fin m → Prop) [DecidableRel E]
    (f : DMFormula (n+m)) (hf : represents E f) (a c : Fin n) (b d : Fin m)
    (ac : a ≠ c) (bd : b ≠ d) (ab : E a b) (ad : E a d) (cb : E c b) (cd : ¬ E c d) :
    3 ≤ uses f (Fin.castAdd m a) + uses f (Fin.natAdd n b) := by
  rw [← pair_uses f _ _ (apart a b)]
  exact switching_cost _ _ _ _ (path_switch E f hf a c b d ac bd ab ad cb cd)

/-- At equality, the duplicate literals lie on a single side of each alternating
cycle. The side may differ between components. -/
theorem optimal_cycle_profile {n} (q : Equiv.Perm (Fin n)) (long : ∀ i, q (q i) ≠ i)
    (f : DMFormula (n+n)) (hf : represents (cycleEdges q) f) (opt : f.leaves = 3*n)
    (i : Fin n) :
    (uses f (Fin.castAdd n i), uses f (Fin.natAdd n i)) =
      (uses f (Fin.castAdd n (q i)), uses f (Fin.natAdd n (q i))) ∧
    ((uses f (Fin.castAdd n i) = 1 ∧ uses f (Fin.natAdd n i) = 2) ∨
     (uses f (Fin.castAdd n i) = 2 ∧ uses f (Fin.natAdd n i) = 1)) := by
  let A (j : Fin n) := uses f (Fin.castAdd n j)
  let B (j : Fin n) := uses f (Fin.natAdd n j)
  have free (j : Fin n) : q j ≠ j := by intro h; exact long j (by simp [h])
  have first (j : Fin n) : 3 ≤ A j + B j := by
    apply path_occurrences _ f hf j (q.symm j) j (q j)
    · intro h; exact free j ((congrArg q h).trans (q.apply_symm_apply j))
    · exact (free j).symm
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr (q.apply_symm_apply j).symm
    · rintro (he|he)
      · exact long j ((congrArg q he).trans (q.apply_symm_apply j))
      · exact free j (he.trans (q.apply_symm_apply j))
  have second (j : Fin n) : 3 ≤ A j + B (q j) := by
    apply path_occurrences _ f hf j (q j) (q j) j (free j).symm (free j)
      (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
    rintro (h|h)
    · exact free j h.symm
    · exact long j h.symm
  have total : ∑ j, A j + ∑ j, B j = 3*n := by
    rw [← opt, ← total_uses,Fin.sum_univ_add]
  have tight (z : Fin n → ℕ) (lb : ∀ j, 3 ≤ z j) (h : ∑ j, z j = 3*n) (j : Fin n) : z j = 3 := by
    apply Eq.symm
    apply (Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (f:=fun _ => 3) (g:=z) (fun k _ => lb k)).mp _ j (Finset.mem_univ _)
    simp [h,Nat.mul_comm]
  have h₁ (j : Fin n) := tight _ first (by rwa [Finset.sum_add_distrib]) j
  have h₂ (j : Fin n) := tight _ second (by rwa [Finset.sum_add_distrib,Equiv.sum_comp q B]) j
  have essential := incident_occurs _ f hf (fun j => ⟨j,Or.inl rfl⟩) (fun j => ⟨j,Or.inl rfl⟩)
  have ea : 1 ≤ A i := essential _
  have eb : 1 ≤ B i := essential _
  change (A i,B i) = (A (q i),B (q i)) ∧ ((A i = 1 ∧ B i = 2) ∨ (A i = 2 ∧ B i = 1))
  have h := h₁ i
  have g := h₁ (q i)
  have p := h₂ i
  constructor
  · exact Prod.ext (by omega) (by omega)
  · omega

def gates {n} : DMFormula n → Nat
  | .lit _ _ => 0
  | .and a b | .or a b => gates a + gates b + 1

theorem gates_succ {n} (f : DMFormula n) : gates f + 1 = f.leaves := by
  induction f with
  | lit i s => rfl
  | and a b ha hb | or a b ha hb => simp only [gates,DMFormula.leaves]; omega

theorem cycles_gate_optimum {n} (hn : 0 < n) (q : Equiv.Perm (Fin n))
    (long : ∀ i, q (q i) ≠ i) :
    (∃ f : DMFormula (n+n), represents (cycleEdges q) f ∧ gates f = 3*n-1) ∧
    ∀ f : DMFormula (n+n), represents (cycleEdges q) f → 3*n-1 ≤ gates f := by
  obtain ⟨f,size,valid⟩ := cycles_upper hn q
  constructor
  · exact ⟨f,valid,by have := gates_succ f; omega⟩
  · intro g valid
    have := cycles_lower q long g valid
    have := gates_succ g
    omega

end PEqualNP.Research.PathFormulaCharge

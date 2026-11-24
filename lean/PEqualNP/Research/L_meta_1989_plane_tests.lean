import PEqualNP.Defs

namespace PEqualNP.Research.PlaneTests

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Side := Finset (Fin 13)

def inc (a b : Fin 13) : Prop := (a.val + b.val) % 13 ∈ [0,1,3,9]
instance (a b : Fin 13) : Decidable (inc a b) := inferInstanceAs (Decidable (_ ∈ _))

def avoid (A : Side) : Side := Finset.univ.filter fun b => ∀ a ∈ A, ¬inc a b

theorem symm (a b : Fin 13) : inc a b ↔ inc b a := by simp [inc, Nat.add_comm]

-- It suffices to enumerate sorted quadruples of points, of which there are 715.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem four_points :
    ∀ a b c d : Fin 13, a < b → b < c → c < d →
      (Finset.univ.filter (fun z : Fin 13 =>
        ¬inc a z ∧ ¬inc b z ∧ ¬inc c z ∧ ¬inc d z)).card ≤ 3 := by
  decide +kernel

theorem rectangle (A B : Side) (h : ∀ a ∈ A, ∀ b ∈ B, ¬inc a b) :
    A.card ≤ 3 ∨ B.card ≤ 3 := by
  by_cases small : A.card ≤ 3
  · exact Or.inl small
  apply Or.inr
  obtain ⟨T, sub, size⟩ := Finset.exists_subset_card_eq (s := A) (show 4 ≤ A.card by omega)
  let f := T.orderEmbOfFin size
  have mem (i : Fin 4) : f i ∈ A := sub (T.orderEmbOfFin_mem size i)
  apply le_trans _ (four_points (f 0) (f 1) (f 2) (f 3)
    (f.strictMono (by decide)) (f.strictMono (by decide)) (f.strictMono (by decide)))
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h _ (mem 0) _ hz, h _ (mem 1) _ hz,
    h _ (mem 2) _ hz, h _ (mem 3) _ hz⟩

theorem exact_of_tests (F : Side → Side → Bool)
    (mono : ∀ {A B A' B'}, A ⊆ A' → B ⊆ B' → F A B = true → F A' B' = true)
    (positive : ∀ a b, inc a b → F {a} {b} = true)
    (negative : ∀ A : Side, A.card ≤ 3 → F A (avoid A) = false ∧ F (avoid A) A = false) :
    ∀ A B, F A B = true ↔ ∃ a ∈ A, ∃ b ∈ B, inc a b := by
  intro A B
  constructor
  · intro hv
    by_contra no
    push Not at no
    rcases rectangle A B no with sa | sb
    · have sub : B ⊆ avoid A := fun b hb => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun a ha => no a ha b hb⟩
      have yes := mono (Finset.Subset.refl A) sub hv
      rw [(negative A sa).1] at yes
      contradiction
    · have sub : A ⊆ avoid B := fun a ha => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun b hb ba => no a ha b hb ((symm a b).mpr ba)⟩
      have yes := mono sub (Finset.Subset.refl B) hv
      rw [(negative B sb).2] at yes
      contradiction
  · rintro ⟨a,ha,b,hb,edge⟩
    exact mono (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_subset_iff.mpr hb)
      (positive a b edge)

-- Wire monotonicity, adapted from the project proof of L-meta-610.
private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

private lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk

def input (P L : Side) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)

def product (C : Circuit) (ws : List ℕ) (P L : Side) : Bool :=
  GateOp.and.eval (ws.map fun w => (C.wires (List.ofFn (input P L))).getD w false)

theorem product_mono (C : Circuit) (hm : Monotone2 C) (ws : List ℕ)
    {A B A' B' : Side} (aa : A ⊆ A') (bb : B ⊆ B') :
    product C ws A B = true → product C ws A' B' = true := by
  have le (i : Fin 26) : input A B i = true → input A' B' i = true := by
    by_cases h : i.val < 13
    · simpa [input,h] using (fun hi => aa hi : Fin.ofNat 13 i.val ∈ A → _)
    · simpa [input,h] using (fun hi => bb hi : Fin.ofNat 13 i.val ∈ B → _)
  have initial (z : ℕ) :
      (List.ofFn (input A B)).getD z false = true → (List.ofFn (input A' B')).getD z false = true := by
    by_cases hz : z < 26
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hz),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hz),
        List.getElem_ofFn, List.getElem_ofFn]
      exact le ⟨z,hz⟩
    · simp [List.getD_eq_getElem?_getD, hz]
  have wires := monotone_foldl_wiresStep C.gates (fun g hg => (hm g hg).1) _ _
    (by simp only [List.length_ofFn]) initial
  simp only [product, GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro h i hi
  exact wires i (h i hi)

-- Any witness to the assigned negated bound would also yield a circuit of at
-- most 63 gates computing the exact plane incidence function on every input.
theorem witness_to_exact (C : Circuit) (ws : List ℕ) (hm : Monotone2 C) (len : ws.length ≤ 2)
    (size : C.size < 63) (pos : ∀ a b, inc a b → product C ws {a} {b} = true)
    (neg : ∀ A : Side, A.card ≤ 3 →
      product C ws A (avoid A) = false ∧ product C ws (avoid A) A = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 63 ∧
      ∀ P L : Side, D.eval (List.ofFn (input P L)) = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
  let D : Circuit := ⟨C.gates ++ [⟨.and,ws⟩], 26 + C.size⟩
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hm g h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨Or.inl rfl,len⟩
  · change (C.gates ++ [_]).length ≤ 63
    change C.gates.length < 63 at size
    simpa using size
  · intro P L
    have hlen : (C.wires (List.ofFn (input P L))).length = 26 + C.size := by
      change (List.foldl wiresStep (List.ofFn (input P L)) C.gates).length = _
      have lens (gs : List Gate) (w : List Bool) :
          (gs.foldl wiresStep w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih => simp [List.foldl_cons,ih,wiresStep,Nat.add_comm,Nat.add_left_comm]
      simp [lens,Circuit.size]
    have last : D.eval (List.ofFn (input P L)) = product C ws P L := by
      change ((C.gates ++ [_]).foldl wiresStep _).getD (26 + C.size) false = _
      rw [List.foldl_append]
      exact getD_append_last_eq (C.wires (List.ofFn (input P L))) _ _ hlen
    rw [last]
    exact exact_of_tests _ (fun aa bb => product_mono C hm ws aa bb) pos neg P L

-- The two sets of negative tests and the singleton positives are equivalent
-- to the full truth table, without any assumption on the selected wires.
theorem tests_iff_exact (C : Circuit) (hm : Monotone2 C) (ws : List ℕ) :
    ((∀ a b, inc a b → product C ws {a} {b} = true) ∧
      (∀ A : Side, A.card ≤ 3 → product C ws A (avoid A) = false ∧
        product C ws (avoid A) A = false)) ↔
    (∀ P L : Side, product C ws P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l) := by
  constructor
  · rintro ⟨pos,neg⟩
    exact exact_of_tests _ (fun aa bb => product_mono C hm ws aa bb) pos neg
  · intro exactness
    constructor
    · intro a b edge
      exact (exactness _ _).mpr ⟨a,by simp,b,by simp,edge⟩
    · intro A _
      constructor
      · apply Bool.eq_false_iff.mpr
        intro ht
        obtain ⟨a,ha,b,hb,edge⟩ := (exactness _ _).mp ht
        exact (Finset.mem_filter.mp hb).2 a ha edge
      · apply Bool.eq_false_iff.mpr
        intro ht
        obtain ⟨a,ha,b,hb,edge⟩ := (exactness _ _).mp ht
        exact (Finset.mem_filter.mp ha).2 b hb ((symm a b).mp edge)

-- This premise is the exact posted statement of L-meta-1989.
theorem assigned_implies_small_exact (h : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 63 ∧
      ∀ P L : Side, D.eval (List.ofFn (input P L)) = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
  classical
  by_contra no
  apply h
  intro C ws mono len tests
  by_contra small
  exact no (witness_to_exact C ws mono len (by omega) tests.1 tests.2)

-- For a circuit written as an OR of complete bipartite blocks, with separate
-- OR trees inside each block, the gate budget cannot go below 64.
def neighbours (a : Fin 13) : Side := Finset.univ.filter (inc a)

theorem degree_four : ∀ a : Fin 13, (neighbours a).card = 4 := by decide

theorem common_at_most_one : ∀ a b : Fin 13, a ≠ b →
    ((neighbours a) ∩ (neighbours b)).card ≤ 1 := by decide

def incidences : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun q => inc q.1 q.2

theorem incidence_count : incidences.card = 52 := by decide

theorem block_estimate (A B : Side) (ha : A.Nonempty) (hb : B.Nonempty)
    (complete : ∀ a ∈ A, ∀ b ∈ B, inc a b) :
    (A ×ˢ B).card ≤ 4 ∧ (A ×ˢ B).card + 1 ≤ A.card + B.card := by
  obtain ⟨a,ma⟩ := ha
  obtain ⟨b,mb⟩ := hb
  have ab : B ⊆ neighbours a := fun y hy => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,complete a ma y hy⟩
  have ba : A ⊆ neighbours b := fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(symm x b).mp (complete x hx b mb)⟩
  have fourA := (Finset.card_le_card ba).trans_eq (degree_four b)
  have fourB := (Finset.card_le_card ab).trans_eq (degree_four a)
  have oneA := Finset.card_pos.mpr (show A.Nonempty from ⟨a,ma⟩)
  have oneB := Finset.card_pos.mpr (show B.Nonempty from ⟨b,mb⟩)
  by_cases one : A.card ≤ 1
  · have eq : A.card = 1 := by omega
    simpa [Finset.card_product,eq,Nat.add_comm] using fourB
  · obtain ⟨x,hx,y,hy,xy⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have sub : B ⊆ neighbours x ∩ neighbours y := fun z hz => Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,complete x hx z hz⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _,complete y hy z hz⟩⟩
    have le := (Finset.card_le_card sub).trans (common_at_most_one x y xy)
    have eq : B.card = 1 := by omega
    simpa [Finset.card_product,eq] using fourA

theorem block_cover_lower (F : Finset (Side × Side))
    (ok : ∀ q ∈ F, q.1.Nonempty ∧ q.2.Nonempty ∧ ∀ a ∈ q.1, ∀ b ∈ q.2, inc a b)
    (covers : ∀ a b, inc a b → ∃ q ∈ F, a ∈ q.1 ∧ b ∈ q.2) :
    64 ≤ (∑ q ∈ F, (q.1.card + q.2.card)) - 1 := by
  let area (q : Side × Side) := (q.1 ×ˢ q.2).card
  have est q (hq : q ∈ F) : area q ≤ 4 ∧ area q + 1 ≤ q.1.card + q.2.card :=
    block_estimate _ _ (ok q hq).1 (ok q hq).2.1 (ok q hq).2.2
  have sub : incidences ⊆ F.biUnion (fun q => q.1 ×ˢ q.2) := by
    intro e he
    obtain ⟨q,hq,a,b⟩ := covers e.1 e.2 (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_product.mpr ⟨a,b⟩⟩
  have h52 : 52 ≤ ∑ q ∈ F, area q := by
    rw [← incidence_count]
    exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le)
  have h4 := Finset.sum_le_sum (s := F) (fun q hq => (est q hq).1)
  have hc := Finset.sum_le_sum (s := F) (fun q hq => (est q hq).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at h4
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  rw [Finset.sum_add_distrib]
  omega

theorem block_cover_attains :
    ∃ F : Finset (Side × Side),
      (∀ q ∈ F, q.1.Nonempty ∧ q.2.Nonempty ∧ ∀ a ∈ q.1, ∀ b ∈ q.2, inc a b) ∧
      (∀ a b, inc a b → ∃ q ∈ F, a ∈ q.1 ∧ b ∈ q.2) ∧
      (∑ q ∈ F, (q.1.card + q.2.card)) - 1 = 64 := by
  let star (a : Fin 13) : Side × Side := ({a}, neighbours a)
  refine ⟨Finset.univ.image star, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨Finset.singleton_nonempty a, Finset.card_pos.mp (by rw [degree_four]; decide), ?_⟩
    intro x hx y hy
    obtain rfl := Finset.mem_singleton.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro a b hab
    exact ⟨star a,Finset.mem_image_of_mem _ (Finset.mem_univ a),Finset.mem_singleton_self a,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab⟩⟩
  · have inj : Function.Injective star := by
      intro a b he
      exact Finset.singleton_inj.mp (congrArg Prod.fst he)
    rw [Finset.sum_image (fun a _ b _ he => inj he)]
    simp [star,degree_four]


def pointsOf (x : Fin 26 → Bool) : Side :=
  Finset.univ.filter fun p : Fin 13 => x ⟨p.val,by omega⟩ = true

def linesOf (x : Fin 26 → Bool) : Side :=
  Finset.univ.filter fun l : Fin 13 => x ⟨13 + l.val,by omega⟩ = true

theorem input_surjective (x : Fin 26 → Bool) : input (pointsOf x) (linesOf x) = x := by
  funext i
  by_cases hi : i.val < 13
  · have e : (Fin.ofNat 13 i.val).val = i.val := Nat.mod_eq_of_lt hi
    simp only [input,hi,ite_true,pointsOf,Finset.mem_filter,Finset.mem_univ,true_and,
      Bool.decide_eq_true]
    congr 1
    exact Fin.ext e
  · have e : 13 + (Fin.ofNat 13 i.val).val = i.val := by change 13 + i.val % 13 = _; omega
    simp only [input,hi,ite_false,linesOf,Finset.mem_filter,Finset.mem_univ,true_and,
      Bool.decide_eq_true]
    congr 1
    exact Fin.ext e

theorem exact_on_bits {D : Circuit}
    (h : ∀ P L : Side, D.eval (List.ofFn (input P L)) = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l)
    (x : Fin 26 → Bool) :
    D.eval (List.ofFn x) = true ↔ ∃ p ∈ pointsOf x, ∃ l ∈ linesOf x, inc p l := by
  simpa only [input_surjective] using h (pointsOf x) (linesOf x)

-- The bound also extends to a final AND of two ORs of
-- bipartite blocks. Blocks in the individual factors may contain nonedges.
-- Each point has a factor whose row has no false positives. Restricting each
-- block to those rows gives a cover by genuine incidence blocks. Every point
-- absent from all shared blocks also needs an occurrence in the other factor.
def factorHits {ι : Type*} (F : Finset ι) (use : ι → Bool → Prop) (P L : ι → Side)
    (c : Bool) (A B : Side) : Prop :=
  ∃ i ∈ F, use i c ∧ ∃ p ∈ A, p ∈ P i ∧ ∃ l ∈ B, l ∈ L i

theorem shared_factor_cost {ι : Type*} [DecidableEq ι] (F : Finset ι) (use : ι → Bool → Prop)
    (P L : ι → Side)
    (computes : ∀ A B : Side,
      (factorHits F use P L false A B ∧ factorHits F use P L true A B) ↔
      ∃ p ∈ A, ∃ l ∈ B, inc p l) :
    ∀ U : Side, (∀ p ∈ U, ∀ i ∈ F, p ∈ P i → ¬(use i false ∧ use i true)) →
    64 + U.card ≤ (∑ i ∈ F, ((P i).card + (L i).card)) - 1 := by
  intro U exclusive
  classical
  let tag (p : Fin 13) := decide (factorHits F use P L false {p} (avoid {p}))
  have reject (p : Fin 13) : ¬ factorHits F use P L (tag p) {p} (avoid {p}) := by
    have both : ¬ (factorHits F use P L false {p} (avoid {p}) ∧
        factorHits F use P L true {p} (avoid {p})) := by
      intro h
      obtain ⟨a,ha,b,hb,edge⟩ := (computes _ _).mp h
      exact (Finset.mem_filter.mp hb).2 a ha edge
    by_cases h : factorHits F use P L false {p} (avoid {p})
    · simpa [tag,h] using (fun ht => both ⟨h,ht⟩ : ¬factorHits F use P L true {p} (avoid {p}))
    · simp [tag,h]
  have covered (c : Bool) (p l : Fin 13) (e : inc p l) :
      ∃ i ∈ F, use i c ∧ p ∈ P i ∧ l ∈ L i := by
    have both := (computes {p} {l}).mpr ⟨p,by simp,l,by simp,e⟩
    have h : factorHits F use P L c {p} {l} := by cases c <;> first | exact both.1 | exact both.2
    simpa [factorHits] using h
  let keep (i : ι) := (P i).filter (fun p => use i (tag p))
  let drop (i : ι) := (P i).filter (fun p => ¬use i (tag p))
  have accurate (i : ι) (hi : i ∈ F) (p : Fin 13) (hp : p ∈ keep i)
      (l : Fin 13) (hl : l ∈ L i) : inc p l := by
    obtain ⟨hp',eq⟩ := Finset.mem_filter.mp hp
    by_contra bad
    have mem : l ∈ avoid {p} := by simpa [avoid] using bad
    exact reject p ⟨i,hi,eq,p,by simp,hp',l,mem,hl⟩
  let J := F.filter fun i => (keep i).Nonempty ∧ (L i).Nonempty
  let area (i : ι) := (keep i ×ˢ L i).card
  have est i (hi : i ∈ J) : area i ≤ 4 ∧ area i + 1 ≤ (keep i).card + (L i).card := by
    obtain ⟨hf,k,l⟩ := Finset.mem_filter.mp hi
    exact block_estimate _ _ k l (accurate i hf)
  have sub : incidences ⊆ J.biUnion (fun i => keep i ×ˢ L i) := by
    intro e he
    obtain ⟨i,hf,eq,p,l⟩ := covered (tag e.1) e.1 e.2 (Finset.mem_filter.mp he).2
    have k : e.1 ∈ keep i := Finset.mem_filter.mpr ⟨p,eq⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hf,⟨_,k⟩,⟨_,l⟩⟩,
      Finset.mem_product.mpr ⟨k,l⟩⟩
  have h52 : 52 ≤ ∑ i ∈ J, area i := by
    rw [← incidence_count]
    exact (Finset.card_le_card sub).trans Finset.card_biUnion_le
  have h4 := Finset.sum_le_sum (s := J) (fun i hi => (est i hi).1)
  have hc := Finset.sum_le_sum (s := J) (fun i hi => (est i hi).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at h4
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  have base : 65 ≤ ∑ i ∈ F, ((keep i).card + (L i).card) := by
    apply le_trans _ (Finset.sum_le_sum_of_subset (f := fun i => (keep i).card + (L i).card)
      (show J ⊆ F from Finset.filter_subset _ _))
    rw [Finset.sum_add_distrib]
    omega
  have discarded : U ⊆ F.biUnion drop := by
    intro p hp
    obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < (neighbours p).card by rw [degree_four]; decide)
    obtain ⟨i,hi,eq,pt,_⟩ := covered (!(tag p)) p l (Finset.mem_filter.mp hl).2
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_filter.mpr ⟨pt,?_⟩⟩
    intro other
    apply exclusive p hp i hi pt
    cases h : tag p <;> simp [h] at eq other <;> exact ⟨by assumption,by assumption⟩
  have extra : U.card ≤ ∑ i ∈ F, (drop i).card :=
    (Finset.card_le_card discarded).trans Finset.card_biUnion_le
  have partition (i : ι) : (keep i).card + (drop i).card = (P i).card :=
    Finset.card_filter_add_card_filter_not ..
  have total := Finset.sum_congr (s₁ := F) rfl (fun i _ => partition i)
  simp only [Finset.sum_add_distrib] at total base ⊢
  omega

theorem two_factor_cost {ι : Type*} [DecidableEq ι] (F : Finset ι) (color : ι → Bool)
    (P L : ι → Side)
    (computes : ∀ A B : Side,
      (factorHits F (fun i c => color i = c) P L false A B ∧
       factorHits F (fun i c => color i = c) P L true A B) ↔
      ∃ p ∈ A, ∃ l ∈ B, inc p l) :
    77 ≤ (∑ i ∈ F, ((P i).card + (L i).card)) - 1 := by
  apply shared_factor_cost F (fun i c => color i = c) P L computes Finset.univ
  intro p hp i hi mem h
  exact Bool.noConfusion (h.1.symm.trans h.2)

-- A factor is additive in the point inputs when each acceptance already has
-- a single-point witness on the same line set. Its dependence on the line
-- inputs can be arbitrary. For two such factors, one can replace the final
-- AND by an OR after routing each point to just one of the factors.
theorem partition_factors (f : Bool → Side → Side → Bool)
    (point_witness : ∀ c A B, f c A B = true ↔ ∃ p ∈ A, f c {p} B = true)
    (line_mono : ∀ c p {B B' : Side}, B ⊆ B' → f c {p} B = true → f c {p} B' = true)
    (on : ∀ p l, inc p l → ∀ c, f c {p} {l} = true)
    (off : ∀ p, (f false {p} (avoid {p}) && f true {p} (avoid {p})) = false) :
    ∃ tag : Fin 13 → Bool,
      ∀ A B : Side,
        ((f false (A.filter (fun p => tag p = false)) B ||
          f true (A.filter (fun p => tag p = true)) B) = true) ↔
        ∃ p ∈ A, ∃ l ∈ B, inc p l := by
  let tag (p : Fin 13) := f false {p} (avoid {p})
  have safe (p : Fin 13) : f (tag p) {p} (avoid {p}) = false := by
    have h := off p
    change f (f false {p} (avoid {p})) {p} (avoid {p}) = false
    cases eq : f false {p} (avoid {p})
    · exact eq
    · simpa only [eq,Bool.true_and] using h
  have row (p : Fin 13) (B : Side) : f (tag p) {p} B = true ↔ ∃ l ∈ B, inc p l := by
    constructor
    · intro accept
      by_contra none
      push Not at none
      have sub : B ⊆ avoid {p} := fun l hl => by
        simpa [avoid] using none l hl
      have yes := line_mono (tag p) p sub accept
      rw [safe] at yes
      contradiction
    · rintro ⟨l,hl,e⟩
      exact line_mono (tag p) p (Finset.singleton_subset_iff.mpr hl) (on p l e _)
  refine ⟨tag,?_⟩
  intro A B
  have forward (c : Bool) (h : f c (A.filter (fun p => tag p = c)) B = true) :
      ∃ p ∈ A, ∃ l ∈ B, inc p l := by
    obtain ⟨p,mem,accept⟩ := (point_witness _ _ _).mp h
    obtain ⟨hp,eq⟩ := Finset.mem_filter.mp mem
    exact ⟨p,hp,(row p B).mp (eq.symm ▸ accept)⟩
  rw [Bool.or_eq_true]
  constructor
  · rintro (h|h)
    · exact forward false h
    · exact forward true h
  · rintro ⟨p,hp,e⟩
    have gt := (row p B).mpr e
    have h := (point_witness (tag p) (A.filter (fun q => tag q = tag p)) B).mpr
      ⟨p,Finset.mem_filter.mpr ⟨hp,rfl⟩,gt⟩
    cases eq : tag p with
    | false => exact Or.inl (by simpa only [eq] using h)
    | true => exact Or.inr (by simpa only [eq] using h)

end PEqualNP.Research.PlaneTests

-- Adapted from upstream L_meta_8945 at 624acb3f, under Apache-2.0.
-- Changes localize the read-two hypothesis to individual flags and bound the exceptional set.
import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Research.ReadAmplification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

private def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

private def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

private def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

private def Thin {N : ℕ} (z : Fin (N+N) → Bool) : Prop :=
  ∀ l l' : Fin N, z (Fin.natAdd N l) = true → z (Fin.natAdd N l') = true → l = l'

private lemma thin_pair {N : ℕ} (p l : Fin N) : Thin (pair p l) := by
  intro i j hi hj
  simp only [pair,decide_eq_true_eq] at hi hj
  exact Fin.natAdd_injective _ _ ((hi.resolve_left (Ne.symm (cast_ne_nat p i))).trans (hj.resolve_left (Ne.symm (cast_ne_nat p j))).symm)

private lemma thin_point {N : ℕ} (p : Fin N) : Thin (point p) := by
  intro i j hi
  exact ((cast_ne_nat p i) (of_decide_eq_true hi).symm).elim

private lemma thin_line {N : ℕ} (l : Fin N) : Thin (line l) := by
  intro i j hi hj
  simp [line] at hi hj
  exact hi.trans hj.symm

private lemma plane_support (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hq2 : 2 ≤ q) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  have hpair (p l : Fin N) (h : I p l) : circuitFun (N + N) C (pair p l) = true := by
    rw [hC _ (thin_pair p l), decide_eq_true_eq]
    exact ⟨p, l, h, by simp [pair], by simp [pair]⟩
  have hpoint (p : Fin N) : circuitFun (N + N) C (point p) = false := by
    rw [hC _ (thin_point p), decide_eq_false_iff_not]
    rintro ⟨_, l, _, _, h⟩
    exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline (l : Fin N) : circuitFun (N + N) C (line l) = false := by
    rw [hC _ (thin_line l), decide_eq_false_iff_not]
    rintro ⟨p, _, _, h, _⟩
    exact cast_ne_nat p l (of_decide_eq_true h)
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]


section ReadWitness


open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 2 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness
open PEqualNP.ReadK
private def addGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], n + C.size⟩

private lemma addSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate n C op a b).size = C.size + 1 := by simp [Circuit.size, addGate]

private lemma addAO {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ} (ha : a < n+C.size) (hb : b < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (addGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact hop
  · intro j hj i hi
    change j < (C.gates ++ [_]).length at hj
    change i ∈ ((C.gates ++ [_]).getD j _).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h.2.1 j hj' i hi
    · simp only [List.length_append, List.length_singleton] at hj
      obtain rfl : j = C.gates.length := by omega
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.2.2 g hg
    · obtain rfl := List.mem_singleton.mp hg
      rfl

private lemma evalLast {α : Type} (d : α) (f : GateOp → List α → α) (xs : List α)
    {n : ℕ} (hx : xs.length = n) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    (evalFrom d f (addGate n C op a b).gates xs).getD i d =
    if i = n+C.size then f op [(evalFrom d f C.gates xs).getD a d,(evalFrom d f C.gates xs).getD b d]
    else (evalFrom d f C.gates xs).getD i d := by
  let w := evalFrom d f C.gates xs
  have hl : w.length = n+C.size := by simp [w,evalFrom_length,hx,Circuit.size]
  change (evalFrom d f (C.gates ++ [_]) xs).getD i d = _
  simp only [evalFrom,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
  change (w ++ [f op [w.getD a d,w.getD b d]]).getD i d = if i = n+C.size then _ else w.getD i d
  rcases lt_trichotomy i (n+C.size) with hi | rfl | hi
  · rw [if_neg hi.ne,List.getD_append _ _ _ _ (by omega)]
  · rw [if_pos rfl,List.getD_append_right _ _ _ _ (by omega)]
    simp [hl] <;> rfl
  · rw [if_neg hi.ne',List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private lemma wordLast (n : ℕ) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    words n (addGate n C op a b) i = if i = n+C.size then
      wordOp op [words n C a,words n C b] else words n C i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private lemma boolLast {n : ℕ} (C : Circuit) (z : Fin n → Bool) (op : GateOp) (a b i : ℕ) :
    circuitValue (addGate n C op a b) z i = if i = n+C.size then
      op.eval [circuitValue C z a,circuitValue C z b] else circuitValue C z i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _


/-- Append a self-AND. It uses two copies of each successful proof, at unit gate cost. -/
def square (n : ℕ) (C : Circuit) := addGate n C .and C.output C.output

private lemma squareSize (n : ℕ) (C : Circuit) : (square n C).size = C.size+1 := addSize ..

private lemma squareAO {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (ho : C.output < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (square n C) :=
  addAO h (Or.inl rfl) ho ho

private lemma squareWords (n : ℕ) (C : Circuit) (t : List ℕ) :
    t ∈ words n (square n C) (square n C).output ↔
    ∃ u ∈ words n C C.output, ∃ v ∈ words n C C.output, t = u++v := by
  change t ∈ words n (addGate n C .and C.output C.output) (n+C.size) ↔ _
  rw [wordLast,if_pos rfl]
  rfl

private lemma squareValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) :
    circuitFun n (square n C) z = circuitFun n C z := by
  change circuitValue (addGate n C .and C.output C.output) z (n+C.size) = _
  rw [boolLast, if_pos rfl]
  change ([circuitValue C z C.output,circuitValue C z C.output].all id) = circuitValue C z C.output
  simp

private lemma setList_mem {n : ℕ} {S : Finset (Fin n)} {i : ℕ} :
    i ∈ setList S ↔ ∃ a ∈ S, a.val = i := by
  simp [setList]

private lemma prime_word_uses {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {S : Finset (Fin n)} (hs : IsPrimeImplicant n C S) {i : Fin n} (hi : i ∈ S)
    {t : List ℕ} (ht : t ∈ words n C C.output) (hts : ∀ j ∈ t, j ∈ setList S) :
    1 ≤ t.count i.val := by
  by_contra! hz
  have hn : i.val ∉ t := by
    intro hm
    have := List.count_pos_iff.mpr hm
    omega
  have bad := hs.2 (S.erase i) (Finset.mem_ssubsets.mpr (Finset.erase_ssubset hi))
  have good : circuitValue C (setInput (S.erase i)) C.output = true := by
    apply (value_eq_terms h _ _).mpr
    refine ⟨t,ht,?_⟩
    intro j hj
    obtain ⟨a,ha,e⟩ := setList_mem.mp (hts j hj)
    have ne : a ≠ i := by
      intro he
      subst a
      exact hn (e ▸ hj)
    exact ⟨a,e,decide_eq_true (Finset.mem_erase.mpr ⟨ne,ha⟩)⟩
  change circuitValue C _ C.output = false at bad
  rw [good] at bad
  contradiction

/-- Two self-ANDs and a final self-OR, preserving the function and enforcing a proper OR output. -/
def amplify (n : ℕ) (C : Circuit) : Circuit :=
  let B := square n (square n C)
  addGate n B .or B.output B.output

theorem amplifySize (n : ℕ) (C : Circuit) : (amplify n C).size = C.size+3 := by
  simp [amplify,addSize,squareSize,Nat.add_assoc]

theorem amplifyValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) :
    circuitFun n (amplify n C) z = circuitFun n C z := by
  let B := square n (square n C)
  have e : circuitFun n (amplify n C) z = circuitFun n B z := by
    change circuitValue (addGate n B .or B.output B.output) z (n+B.size) = _
    rw [boolLast,if_pos rfl]
    change ([circuitValue B z B.output,circuitValue B z B.output].any id) = circuitValue B z B.output
    simp
  simpa [B,squareValue] using e

theorem amplifyModel {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (ho : C.output < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (amplify n C) ∧ n ≤ (amplify n C).output ∧
    (amplify n C).output < n+(amplify n C).size ∧
    ∃ g : Gate, (amplify n C).gates[(amplify n C).output - n]? = some g ∧ g.op = .or := by
  let A := square n C
  let B := square n A
  have ha : A.output < n+A.size := by change n+C.size < n+(square n C).size; exact Nat.lt_add_one _ |> fun hh => by simpa only [squareSize,← Nat.add_assoc] using hh
  have hb : B.output < n+B.size := by change n+A.size < n+(square n A).size; exact Nat.lt_add_one _ |> fun hh => by simpa only [squareSize,← Nat.add_assoc] using hh
  have hao := squareAO h ho
  have hbo := squareAO hao ha
  refine ⟨addAO hbo (Or.inr rfl) hb hb, by change n ≤ n+B.size; omega, ?_, ?_⟩
  · change n+B.size < n+(addGate n B .or B.output B.output).size
    rw [addSize]; omega
  · refine ⟨⟨.or,[B.output,B.output]⟩,?_,rfl⟩
    change (B.gates ++ [_])[n+B.size-n]? = _
    simp [Circuit.size,B,A]

theorem amplifyHard {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (ho : C.output < n+C.size)
    {S : Finset (Fin n)} (hp : IsPrimeImplicant n C S) (hne : S.Nonempty) :
    readsAtMost (amplify n C) n (setList S) 2 = false := by
  let A := square n C
  let B := square n A
  cases r : readsAtMost (amplify n C) n (setList S) 2 with
  | false => rfl
  | true =>
    obtain ⟨t,ht,hs,hcount⟩ := read_to_terms (amplifyModel h ho).1 _ r
    change t ∈ words n (addGate n B .or B.output B.output) (n+B.size) at ht
    rw [wordLast,if_pos rfl] at ht
    have htB : t ∈ words n B B.output := ht.elim id id
    obtain ⟨u,hu,v,hv,rfl⟩ := (squareWords n A t).mp htB
    obtain ⟨a,ha,b,hb,rfl⟩ := (squareWords n C u).mp hu
    obtain ⟨c,hc,d,hd,rfl⟩ := (squareWords n C v).mp hv
    obtain ⟨i,hi⟩ := hne
    have low (w : List ℕ) (hw : w ∈ words n C C.output)
        (incl : ∀ j ∈ w, j ∈ ((a++b)++(c++d))) : 1 ≤ w.count i.val :=
      prime_word_uses h hp hi hw (fun j hj => hs j (incl j hj))
    have h1 := low a ha (by simp_all)
    have h2 := low b hb (by simp_all)
    have h3 := low c hc (by simp_all)
    have h4 := low d hd (by simp_all)
    have high := hcount i.val (setList_mem.mpr ⟨i,hi,rfl⟩)
    simp only [List.count_append] at high
    omega

end PEqualNP.Research.ReadAmplification

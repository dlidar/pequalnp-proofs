import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import PEqualNP.Defs.TwoColour
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-!
# Partial results for L-meta-4675

For a disjunction of sound rectangles, shared OR preprocessing still costs
enough to obtain the edge-plus-cover lower bound. For nested monotone operands
whose conjunction implies the target, their off-target pair sets must satisfy
a crossing condition. An off-target rectangle on one side confines all
opposite off-target pairs to one row and one column. More generally one
operand has a cover of at most four vertices for its off-target pairs.
Two operands cannot both have five disjoint off-target pairs: two-colouring
the 5 by 5 crossing grid would force a target four-cycle. An explicit
pair of graph operands needs all four covering vertices on each side.
The gate-count argument for unrestricted nesting remains open.

The full circuit evaluator is used in the endpoint bound, the monotone-wire
result, and the matching example. The project also treats pair-clean circuits
in the auxiliary cleanBound theorem in L_meta_1892.
-/

namespace PEqualNP.Research.StarNetworks

open Finset

-- A wire denotes a set of leaves. Raw wires have at most one leaf.
-- Expanding several output wires backwards counts a shared union gate once.
theorem leaves_le {V : Type*} [DecidableEq V] (n s : ℕ) (W : ℕ → Finset V)
    (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (T : Finset V) (F : Finset ℕ)
    (valid : ∀ i ∈ F, i < n+s) (inside : ∀ i ∈ F, W i ⊆ T) :
    (F.biUnion W).card ≤ F.card +
      ((range s).filter fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ T).card := by
  classical
  induction s generalizing F with
  | zero =>
    have bound := card_biUnion_le (s := F) (t := W)
    have h := sum_le_sum (s := F) (g := fun _ => 1) (fun i hi => raw i (by simpa using valid i hi))
    simpa using bound.trans h
  | succ s ih =>
    let k := n+s
    let good := fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ T
    let c := ((range s).filter good).card
    have count : ((range (s+1)).filter good).card = c + (if good s then 1 else 0) := by
      rw [range_add_one,filter_insert]
      split <;> simp_all [c]
    change _ ≤ F.card + ((range (s+1)).filter good).card
    rw [count]
    have prev := ih (fun j hj => gate j (by omega))
    by_cases hit : k ∈ F
    · let R := F.erase k
      have size : R.card + 1 = F.card := card_erase_add_one hit
      have vr : ∀ i ∈ R, i < k := by
        intro i hi
        obtain ⟨ne,h⟩ := mem_erase.mp hi
        have := valid i h
        dsimp [k] at *; omega
      have ir : ∀ i ∈ R, W i ⊆ T := fun i hi => inside i (mem_of_mem_erase hi)
      have eq : F = insert k R := (insert_erase hit).symm
      by_cases big : 1 < (W k).card
      · obtain ⟨a,b,ha,hb,e⟩ := gate s (by omega)
        let G := insert a (insert b R)
        have step := prev G (by
          intro i hi
          simp only [G, mem_insert] at hi
          rcases hi with rfl|rfl|h
          · exact ha
          · exact hb
          · exact vr _ h) (by
          have h := inside k hit
          rw [show W k = W a ∪ W b from e] at h
          intro i hi
          simp only [G, mem_insert] at hi
          rcases hi with rfl|rfl|hi
          · exact (subset_union_left).trans h
          · exact (subset_union_right).trans h
          · exact ir _ hi)
        change (G.biUnion W).card ≤ G.card + c at step
        have same : F.biUnion W = G.biUnion W := by
          rw [eq,biUnion_insert,show W k = W a ∪ W b from e]
          simp [G,union_assoc]
        have c1 := card_insert_le a (insert b R)
        have c2 := card_insert_le b R
        have hs : good s := ⟨big,inside k hit⟩
        rw [same,ite_eq_left hs]; dsimp [G] at step ⊢; omega
      · have step := prev R vr ir
        change (R.biUnion W).card ≤ R.card+c at step
        have add := card_union_le (W k) (R.biUnion W)
        rw [eq,biUnion_insert]
        have fresh : k ∉ R := notMem_erase _ _
        rw [card_insert_of_notMem fresh]
        omega
    · have v : ∀ i ∈ F, i < n+s := by
        intro i hi
        have := valid i hi
        have ne : i ≠ k := fun e => hit (e ▸ hi)
        dsimp [k] at ne; omega
      have step := prev F v inside
      change (F.biUnion W).card ≤ F.card+c at step
      omega

-- The sum is over distinct centers. A nontrivial shared union can belong
-- to only one neighborhood, even if several terms use the same center.
theorem star_leaf_count {V : Type*} [DecidableEq V] (n s m : ℕ)
    (W : ℕ → Finset V) (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (hood : V → Finset V) (thin : ∀ a b, a ≠ b → (hood a ∩ hood b).card ≤ 1)
    (center : Fin m → V) (arm : Fin m → ℕ) (valid : ∀ j, arm j < n+s)
    (sound : ∀ j, W (arm j) ⊆ hood (center j)) :
    let centers := univ.image center
    let arms := fun c => (univ.filter fun j => center j = c).image arm
    ∑ c ∈ centers, ((arms c).biUnion W).card ≤ m+s := by
  classical
  intro centers arms
  let active := fun c => (range s).filter fun j => 1 < (W (n+j)).card ∧ W (n+j) ⊆ hood c
  have each (c) : ((arms c).biUnion W).card ≤
      (univ.filter fun j => center j = c).card + (active c).card := by
    apply le_trans (leaves_le n s W raw gate (hood c) (arms c) ?_ ?_)
    · exact Nat.add_le_add_right card_image_le _
    · intro i hi
      obtain ⟨j,_,rfl⟩ := mem_image.mp hi
      exact valid _
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      rw [←(mem_filter.mp hj).2]
      exact sound _
  have disj : (centers : Set V).PairwiseDisjoint active := by
    intro a _ b _ ne
    apply disjoint_left.mpr
    intro j ja jb
    obtain ⟨_,big,ha⟩ := mem_filter.mp ja
    obtain ⟨_,_,hb⟩ := mem_filter.mp jb
    exact (Nat.not_lt_of_ge ((card_le_card (subset_inter ha hb)).trans (thin a b ne))) big
  have total : ∑ c ∈ centers, (active c).card ≤ s := by
    rw [←card_biUnion disj]
    apply le_trans (card_le_card (t := range s) ?_) (by simp)
    intro j h
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hc).1
  calc
    _ ≤ _ := sum_le_sum (fun c _ => each c)
    _ = _ := sum_add_distrib
    _ ≤ m+s := by
      rw [sum_card_fiberwise_eq_card_filter]
      have h := card_le_card (filter_subset (fun i => center i ∈ centers) (univ : Finset (Fin m)))
      simp only [card_univ,Fintype.card_fin] at h
      omega

abbrev Vertex (p l : ℕ) := Fin p ⊕ Fin l

def adjacent {p l} (E : Finset (Fin p × Fin l)) : Vertex p l → Vertex p l → Prop
  | .inl a, .inr b => (a,b) ∈ E
  | .inr b, .inl a => (a,b) ∈ E
  | _, _ => False

noncomputable def hoodOf {p l} (E : Finset (Fin p × Fin l)) (c : Vertex p l) : Finset (Vertex p l) := by
  classical
  exact univ.filter (adjacent E c)

theorem hood_thin {p l} (E : Finset (Fin p × Fin l))
    (no4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
       ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (c d : Vertex p l) (ne : c ≠ d) : (hoodOf E c ∩ hoodOf E d).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro v hv w hw
  cases c <;> cases d <;> cases v <;> cases w <;>
    simp_all [hoodOf,adjacent]

  · by_contra h
    exact no4 _ _ _ _ ne h hv.1 hw.1 hv.2 hw.2
  · by_contra h
    exact no4 _ _ _ _ h ne hv.1 hv.2 hw.1 hw.2

def decode {p l} : Vertex p l × Vertex p l → Option (Fin p × Fin l)
  | (.inl a,.inr b) => some (a,b)
  | (.inr b,.inl a) => some (a,b)
  | _ => none

-- Each term is the AND of a center input with one leaf-union wire. Terms
-- may overlap, repeat centers, and share gates anywhere in the union network.
-- Connecting m terms by binary OR takes m-1 gates for m positive.
theorem star_network_bound (p l n s m : ℕ) (E : Finset (Fin p × Fin l))
    (no4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (W : ℕ → Finset (Vertex p l)) (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (center : Fin m → Vertex p l) (arm : Fin m → ℕ) (valid : ∀ j, arm j < n+s)
    (sound : ∀ j, W (arm j) ⊆ hoodOf E (center j))
    (complete : ∀ e ∈ E, ∃ j v, v ∈ W (arm j) ∧ decode (center j,v) = some e) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ (s + m + (m-1)) + 1 := by
  classical
  let centers := univ.image center
  let arms := fun c => (univ.filter fun j => center j = c).image arm
  let leaves := fun c => (arms c).biUnion W
  let oriented := centers.biUnion fun c => (leaves c).image fun v => (c,v)
  have counts := star_leaf_count n s m W raw gate (hoodOf E) (hood_thin E no4) center arm valid sound
  change ∑ c ∈ centers, (leaves c).card ≤ m+s at counts
  have ecount : E.card ≤ oriented.card := by
    have sub : E.image some ⊆ oriented.image decode := by
      intro x hx
      obtain ⟨e,he,rfl⟩ := mem_image.mp hx
      obtain ⟨j,v,hv,eq⟩ := complete e he
      apply mem_image.mpr
      refine ⟨(center j,v),mem_biUnion.mpr ⟨center j,mem_image.mpr ⟨j,mem_univ _,rfl⟩,?_⟩,eq⟩
      apply mem_image.mpr
      exact ⟨v,mem_biUnion.mpr ⟨arm j,mem_image.mpr ⟨j,by simp,rfl⟩,hv⟩,rfl⟩
    have bnd := (card_le_card sub).trans card_image_le
    simpa only [card_image_of_injective E (fun _ _ h => Option.some.inj h)] using bnd
  have oc : oriented.card ≤ ∑ c ∈ centers, (leaves c).card := by
    apply le_trans card_biUnion_le
    exact sum_le_sum fun _ _ => card_image_le
  let S := centers.image (finSumFinEquiv : Vertex p l ≃ Fin (p+l))
  refine ⟨S,?_,?_⟩
  · intro a b he
    obtain ⟨j,v,hv,eq⟩ := complete (a,b) he
    have h : finSumFinEquiv (center j) ∈ S :=
      mem_image.mpr ⟨_,mem_image.mpr ⟨j,mem_univ _,rfl⟩,rfl⟩
    cases c : center j <;> cases v <;> simp [c,decode] at eq h
    · obtain ⟨rfl,rfl⟩ := eq
      exact Or.inl h
    · obtain ⟨rfl,rfl⟩ := eq
      exact Or.inr h
  · have sc : S.card ≤ centers.card := card_image_le
    have cc : centers.card ≤ m := by
      exact (card_image_le (f := center) (s := univ)).trans (by simp)
    omega

-- Two monochromatic OR expressions feeding an AND form a rectangle.
-- Soundness and the four-cycle hypothesis force a singleton side. All OR
-- expressions can draw from one shared gate list, across all the rectangles.
theorem rectangle_network_bound (p l n s m : ℕ) (E : Finset (Fin p × Fin l))
    (no4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (W : ℕ → Finset (Vertex p l)) (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (x y : Fin m → ℕ) (valid : ∀ j, x j < n+s ∧ y j < n+s)
    (used : ∀ j, (W (x j)).Nonempty ∧ (W (y j)).Nonempty)
    (sound : ∀ j u, u ∈ W (x j) → ∀ v ∈ W (y j), adjacent E u v)
    (complete : ∀ e ∈ E, ∃ j u v, u ∈ W (x j) ∧ v ∈ W (y j) ∧ decode (u,v) = some e) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ (s + m + (m-1)) + 1 := by
  classical
  have symm (u v : Vertex p l) : adjacent E u v ↔ adjacent E v u := by
    cases u <;> cases v <;> rfl
  have swap (u v : Vertex p l) : decode (u,v) = decode (v,u) := by
    cases u <;> cases v <;> rfl
  have term (j : Fin m) : ∃ c k, k < n+s ∧ W k ⊆ hoodOf E c ∧
      ∀ u ∈ W (x j), ∀ v ∈ W (y j), ∃ t ∈ W k, decode (c,t) = decode (u,v) := by
    by_cases small : (W (x j)).card ≤ 1
    · obtain ⟨c,hc⟩ := (used j).1
      refine ⟨c,y j,(valid j).2,?_,?_⟩
      · intro v hv
        exact mem_filter.mpr ⟨mem_univ _,sound j c hc v hv⟩
      · intro u hu v hv
        have eq := card_le_one.mp small u hu c hc
        subst u
        exact ⟨v,hv,rfl⟩
    · obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge small)
      have incl : W (y j) ⊆ hoodOf E a ∩ hoodOf E b := by
        intro v hv
        exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,sound j a ha v hv⟩,
          mem_filter.mpr ⟨mem_univ _,sound j b hb v hv⟩⟩
      have narrow := (card_le_card incl).trans (hood_thin E no4 a b ne)
      obtain ⟨c,hc⟩ := (used j).2
      refine ⟨c,x j,(valid j).1,?_,?_⟩
      · intro u hu
        exact mem_filter.mpr ⟨mem_univ _,(symm _ _).mp (sound j u hu c hc)⟩
      · intro u hu v hv
        have eq := card_le_one.mp narrow v hv c hc
        subst v
        exact ⟨u,hu,swap _ _⟩
  choose center arm validArm armSound covers using term
  apply star_network_bound p l n s m E no4 W raw gate center arm validArm armSound
  intro e he
  obtain ⟨j,u,v,hu,hv,eq⟩ := complete e he
  obtain ⟨t,ht,et⟩ := covers j u hu v hv
  exact ⟨j,t,ht,et.trans eq⟩


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Backward slicing for the project's actual circuit evaluator. Reads of
-- unavailable wires return false, so they do not require a validity assumption.
theorem circuit_support (n : ℕ) (C : Circuit) (binary : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ T : Finset ℕ, T.card ≤ C.size+1 ∧
      ∀ x y : Fin n → Bool, (∀ i : Fin n, i.val ∈ T → x i = y i) →
        circuitFun n C x = circuitFun n C y := by
  classical
  let run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w
  have len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run,Circuit.wires]
    | cons g gs ih =>
      change (run gs (w ++ [_])).length = _
      rw [ih]; simp; omega
  have appendVal (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases h : i = w.length
    · subst i; simp
    · rw [ite_eq_right h]
      by_cases lt : i < w.length
      · exact List.getD_append _ _ _ _ lt
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
  have cut (gs : List Gate) (ok : ∀ g ∈ gs, g.inputs.length ≤ 2) (F : Finset ℕ) :
      ∃ T : Finset ℕ, T.card ≤ gs.length+F.card ∧
        ∀ x y : Fin n → Bool, (∀ i : Fin n, i.val ∈ T → x i = y i) →
        ∀ i ∈ F, (run gs (List.ofFn x)).getD i false = (run gs (List.ofFn y)).getD i false := by
    induction gs using List.reverseRecOn generalizing F with
    | nil =>
      refine ⟨F,by simp,?_⟩
      intro x y same i hi
      by_cases lt : i < n
      · simpa [run,Circuit.wires,List.getD_eq_getElem,lt] using same ⟨i,lt⟩ hi
      · simp [run,Circuit.wires,List.getD_eq_getElem?_getD,lt]
    | append_singleton gs g ih =>
      let k := n+gs.length
      let G := if k ∈ F then F.erase k ∪ g.inputs.toFinset else F
      obtain ⟨T,ts,det⟩ := ih (fun a ha => ok a (by simp [ha])) G
      have bound : G.card ≤ F.card+1 := by
        dsimp [G]
        split
        · rename_i mem
          have ec := card_erase_add_one mem
          have un := card_union_le (F.erase k) g.inputs.toFinset
          have small := (List.toFinset_card_le (l := g.inputs)).trans (ok g (by simp))
          omega
        · omega
      refine ⟨T,by simp; omega,?_⟩
      intro x y same i hi
      simp only [run,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,appendVal]
      change (if i = (run gs (List.ofFn x)).length then _ else _) =
        (if i = (run gs (List.ofFn y)).length then _ else _)
      rw [len,len,List.length_ofFn,List.length_ofFn]
      by_cases last : i = k
      · subst i
        rw [ite_eq_left rfl,ite_eq_left rfl]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact det x y same a (by simp [G,hi,ha])
      · rw [ite_eq_right last,ite_eq_right last]
        exact det x y same i (by by_cases h : k ∈ F <;> simp [G,h,hi,last])
  obtain ⟨T,ts,det⟩ := cut C.gates binary {C.output}
  exact ⟨T,by simpa [Circuit.size] using ts,fun x y same => det x y same C.output (by simp)⟩

-- Every endpoint of an actual edge is essential in the assigned edge function.
theorem endpoint_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (binary : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (computes : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ((E.image Prod.fst).card + (E.image Prod.snd).card) ≤ C.size+1 := by
  classical
  obtain ⟨T,tcard,det⟩ := circuit_support (p+l) C binary
  have sep (a : Fin p) (b : Fin l) : Fin.castAdd l a ≠ Fin.natAdd p b := by
    intro e
    have h := congrArg Fin.val e
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    have := a.isLt
    omega
  have both (a : Fin p) (b : Fin l) (ab : (a,b) ∈ E) : a.val ∈ T ∧ p+b.val ∈ T := by
    let u := Fin.castAdd l a
    let v := Fin.natAdd p b
    let pair := fun i : Fin (p+l) => decide (i=u ∨ i=v)
    let single := fun i j : Fin (p+l) => decide (j=i)
    have yes : circuitFun (p+l) C pair = true := by
      rw [computes,decide_eq_true_eq]
      exact ⟨a,b,ab,by simp [pair,u],by simp [pair,v]⟩
    have no (k : Fin (p+l)) : circuitFun (p+l) C (single k) = false := by
      rw [computes,decide_eq_false_iff_not]
      rintro ⟨c,d,_,hc,hd⟩
      exact sep c d ((of_decide_eq_true hc).trans (of_decide_eq_true hd).symm)
    constructor
    · by_contra miss
      have same := det pair (single v) (by
        intro i hi
        have h : i ≠ u := fun e => miss (show u.val ∈ T from e ▸ hi)
        simp [pair,single,h])
      rw [yes,no] at same
      contradiction
    · by_contra miss
      have same := det pair (single u) (by
        intro i hi
        have h : i ≠ v := fun e => miss (show v.val ∈ T from e ▸ hi)
        simp [pair,single,h])
      rw [yes,no] at same
      contradiction
  let A := (E.image Prod.fst).image Fin.val
  let B := (E.image Prod.snd).image (fun b : Fin l => p+b.val)
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro i hi hj
    obtain ⟨a,_,rfl⟩ := mem_image.mp hi
    obtain ⟨b,_,eq⟩ := mem_image.mp hj
    have := a.isLt
    omega
  have includeBoth : A ∪ B ⊆ T := by
    intro i hi
    rcases mem_union.mp hi with ha|hb
    · obtain ⟨a,he,rfl⟩ := mem_image.mp ha
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp he
      exact (both _ _ hab).1
    · obtain ⟨b,he,rfl⟩ := mem_image.mp hb
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp he
      exact (both _ _ hab).2
  have h := (card_le_card includeBoth).trans tcard
  rw [card_union_of_disjoint dis] at h
  have inj : Function.Injective (fun b : Fin l => p+b.val) := fun a b e => Fin.ext (Nat.add_left_cancel e)
  simpa only [A,B,card_image_of_injective _ Fin.val_injective,card_image_of_injective _ inj] using h

-- The full assigned conclusion when points have degree at most one. Different
-- line stars may have arbitrary sizes, and C can have arbitrary gate depth.
theorem line_star_forest_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (forest : Set.InjOn Prod.fst (E : Set (Fin p × Fin l)))
    (binary : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (computes : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size+1 := by
  classical
  refine ⟨(E.image Prod.snd).image (Fin.natAdd p),?_,?_⟩
  · intro a b e
    exact Or.inr (mem_image.mpr ⟨b,mem_image.mpr ⟨(a,b),e,rfl⟩,rfl⟩)
  · have h := endpoint_bound p l E C binary computes
    rw [card_image_of_injOn forest] at h
    exact (Nat.add_le_add_left card_image_le _).trans h

-- The following criterion handles a nested AND whose operands are themselves
-- disjunctions of edges. It checks every input using only assignments with at
-- most two points and two lines on, without assuming anything about degrees.
def hits {p l : ℕ} (F : Finset (Fin p × Fin l)) (P : Fin p → Prop) (L : Fin l → Prop) : Prop :=
  ∃ a b, (a,b) ∈ F ∧ P a ∧ L b

theorem nested_and_exact {p l : ℕ} (E F G : Finset (Fin p × Fin l)) :
    (∀ P L, (hits F P L ∧ hits G P L) ↔ hits E P L) ↔
    E = F ∩ G ∧ ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E := by
  classical
  constructor
  · intro exactGraph
    refine ⟨?_,?_⟩
    · ext e
      rcases e with ⟨a,b⟩
      simpa [hits] using (exactGraph (fun v => v = a) (fun v => v = b)).symm
    · intro a b c d ha badA hc badC
      have shown := (exactGraph (fun v => v=a ∨ v=c) (fun v => v=b ∨ v=d)).mp
        ⟨⟨a,b,ha,Or.inl rfl,Or.inl rfl⟩,⟨c,d,hc,Or.inr rfl,Or.inr rfl⟩⟩
      obtain ⟨i,j,edge,hi,hj⟩ := shown
      rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> tauto
  · rintro ⟨same,cross⟩ P L
    constructor
    · rintro ⟨⟨a,b,hf,ap,bp⟩,⟨c,d,hg,cp,dp⟩⟩
      by_cases e : (a,b) ∈ E
      · exact ⟨a,b,e,ap,bp⟩
      by_cases f : (c,d) ∈ E
      · exact ⟨c,d,f,cp,dp⟩
      rcases cross a b c d hf e hg f with h|h
      · exact ⟨a,d,h,ap,dp⟩
      · exact ⟨c,b,h,cp,bp⟩
    · rintro ⟨a,b,he,ap,bp⟩
      rw [same,mem_inter] at he
      exact ⟨⟨a,b,he.1,ap,bp⟩,⟨a,b,he.2,ap,bp⟩⟩

-- Four off-target edges forming a rectangle in the first operand force
-- every off-target edge of the second operand to meet at most two fixed
-- vertices. This concerns graph-valued operands of an exact final AND.
theorem cross_extras_cover {p l : ℕ} (E F G : Finset (Fin p × Fin l))
    (no4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
       (a,d) ∈ E ∨ (c,b) ∈ E)
    (a a' : Fin p) (b b' : Fin l) (da : a ≠ a') (db : b ≠ b')
    (rect : ∀ i ∈ ({a,a'} : Finset (Fin p)), ∀ j ∈ ({b,b'} : Finset (Fin l)), (i,j) ∈ F \ E) :
    ∃ (R : Finset (Fin p)) (B : Finset (Fin l)), R.card ≤ 1 ∧ B.card ≤ 1 ∧
      ∀ i j, (i,j) ∈ G \ E → i ∈ R ∨ j ∈ B := by
  classical
  let rows := univ.filter fun i : Fin p => (i,b) ∈ E ∧ (i,b') ∈ E
  let cols := univ.filter fun j : Fin l => (a,j) ∈ E ∧ (a',j) ∈ E
  have hr : rows.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi k hk
    by_contra ne
    obtain ⟨_,ib,ib'⟩ := mem_filter.mp hi
    obtain ⟨_,kb,kb'⟩ := mem_filter.mp hk
    exact no4 i k b b' ne db ⟨ib,ib',kb,kb'⟩
  have hc : cols.card ≤ 1 := by
    apply card_le_one.mpr
    intro j hj k hk
    by_contra ne
    obtain ⟨_,aj,aj'⟩ := mem_filter.mp hj
    obtain ⟨_,ak,ak'⟩ := mem_filter.mp hk
    exact no4 a a' j k da ne ⟨aj,ak,aj',ak'⟩
  refine ⟨rows,cols,hr,hc,?_⟩
  intro i j hij
  obtain ⟨g,off⟩ := mem_sdiff.mp hij
  by_cases hcol : j ∈ cols
  · exact Or.inr hcol
  · have missing : ∃ r ∈ ({a,a'} : Finset (Fin p)), (r,j) ∉ E := by
      by_cases h : (a,j) ∈ E
      · exact ⟨a',by simp, fun h' => hcol (mem_filter.mpr ⟨mem_univ _,h,h'⟩)⟩
      · exact ⟨a,by simp,h⟩
    obtain ⟨r,hr,miss⟩ := missing
    have row (t) (ht : t ∈ ({b,b'} : Finset (Fin l))) : (i,t) ∈ E := by
      obtain ⟨positive,negative⟩ := mem_sdiff.mp (rect r hr t ht)
      exact (cross r t i j positive negative g off).resolve_left miss
    have hrow : i ∈ rows := mem_filter.mpr ⟨mem_univ _,row b (by simp),row b' (by simp)⟩
    exact Or.inl hrow

def fourFree {p l} (H : Finset (Fin p × Fin l)) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' →
    ¬ ((a,b) ∈ H ∧ (a,b') ∈ H ∧ (a',b) ∈ H ∧ (a',b') ∈ H)

theorem cover_cross_is_fourFree {p l} (H : Finset (Fin p × Fin l))
    (R : Finset (Fin p)) (B : Finset (Fin l)) (hr : R.card ≤ 1) (hb : B.card ≤ 1)
    (covers : ∀ i j, (i,j) ∈ H → i ∈ R ∨ j ∈ B) : fourFree H := by
  intro i i' j j' di dj rect
  obtain ⟨h00,h01,h10,h11⟩ := rect
  have row (i : Fin p) (h : (i,j) ∈ H) (h' : (i,j') ∈ H) : i ∈ R := by
    by_contra off
    exact dj (card_le_one.mp hb _ ((covers i j h).resolve_left off) _ ((covers i j' h').resolve_left off))
  exact di (card_le_one.mp hr _ (row _ h00 h01) _ (row _ h10 h11))

-- Here F and G need only be the pair footprints of the operands. An
-- arbitrary monotone wire may also accept assignments requiring more bits.
theorem cross_dichotomy {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E) : fourFree (F \ E) ∨ fourFree (G \ E) := by
  classical
  by_cases hf : fourFree (F \ E)
  · exact Or.inl hf
  · unfold fourFree at hf
    push Not at hf
    obtain ⟨a,a',b,b',da,db,h00,h01,h10,h11⟩ := hf
    have rect : ∀ i ∈ ({a,a'} : Finset (Fin p)), ∀ j ∈ ({b,b'} : Finset (Fin l)), (i,j) ∈ F \ E := by
      intro i hi j hj
      simp only [mem_insert,mem_singleton] at hi hj
      rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> assumption
    obtain ⟨R,B,hr,hb,cover⟩ := cross_extras_cover E F G no4 cross a a' b b' da db rect
    exact Or.inr (cover_cross_is_fourFree _ _ _ hr hb cover)

def wireAccepts {p l} (C : Circuit) (w : ℕ) (P : Finset (Fin p)) (L : Finset (Fin l)) : Prop :=
  (C.wires (List.ofFn (Fin.append (fun a => decide (a ∈ P)) (fun b => decide (b ∈ L))))).getD w false = true

noncomputable def footprint (p l : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin p × Fin l) := by
  classical
  exact univ.filter fun e => wireAccepts C w {e.1} {e.2}

theorem wireAccepts_mono {p l} (C : Circuit) (hC : IsMonotoneCircuit C) (w : ℕ)
    {P P' : Finset (Fin p)} {L L' : Finset (Fin l)} (hp : P ⊆ P') (hl : L ⊆ L') :
    wireAccepts C w P L → wireAccepts C w P' L' := by
  apply LowMergeProof.wires_mono C hC _ _ (by simp) _ w
  intro i
  by_cases h : i < p+l
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
    let k : Fin (p+l) := ⟨i,h⟩
    change Fin.append _ _ k = true → Fin.append _ _ k = true
    induction k using Fin.addCases with
    | left a => simpa only [Fin.append_left,decide_eq_true_eq] using (fun hx => hp hx : a ∈ P → a ∈ P')
    | right b => simpa only [Fin.append_right,decide_eq_true_eq] using (fun hx => hl hx : b ∈ L → b ∈ L')
  · simp [List.getD_eq_getElem?_getD,h]

-- Turning on both input pairs forces a true cross edge, for arbitrary
-- monotone wires even when neither operand computes a graph function.
theorem sound_wire_cross {p l} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    ∀ a b c d, (a,b) ∈ footprint p l C u → (a,b) ∉ E →
      (c,d) ∈ footprint p l C v → (c,d) ∉ E → (a,d) ∈ E ∨ (c,b) ∈ E := by
  classical
  intro a b c d ha badA hc badC
  have left := (mem_filter.mp ha).2
  have right := (mem_filter.mp hc).2
  have joined := sound ({a,c} : Finset (Fin p)) ({b,d} : Finset (Fin l))
    (wireAccepts_mono C hC u (by simp : ({a} : Finset _) ⊆ {a,c}) (by simp : ({b} : Finset _) ⊆ {b,d}) left)
    (wireAccepts_mono C hC v (by simp : ({c} : Finset _) ⊆ {a,c}) (by simp : ({d} : Finset _) ⊆ {b,d}) right)
  obtain ⟨i,hi,j,hj,edge⟩ := joined
  simp only [mem_insert,mem_singleton] at hi hj
  rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> tauto

-- All the other operand's false positives touch one fixed point or one
-- fixed line as soon as the first contains an entire off-target rectangle.
theorem sound_wire_rectangle_cover {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E)
    (a a' : Fin p) (b b' : Fin l) (da : a ≠ a') (db : b ≠ b')
    (rect : ∀ i ∈ ({a,a'} : Finset (Fin p)), ∀ j ∈ ({b,b'} : Finset (Fin l)),
      (i,j) ∈ footprint p l C u \ E) :
    ∃ (R : Finset (Fin p)) (B : Finset (Fin l)), R.card ≤ 1 ∧ B.card ≤ 1 ∧
      ∀ i j, (i,j) ∈ footprint p l C v \ E → i ∈ R ∨ j ∈ B :=
  cross_extras_cover E _ _ no4 (sound_wire_cross E C hC u v sound) a a' b b' da db rect

theorem sound_wire_pair_dichotomy {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    fourFree (footprint p l C u \ E) ∨ fourFree (footprint p l C v \ E) :=
  cross_dichotomy E _ _ no4 (sound_wire_cross E C hC u v sound)

-- For any sound AND, removing at most six input vertices clears every
-- off-target point-line pair from at least one operand. Three independent
-- errors on one side force the six covering vertices on the opposite side.
def smallCover {p l} (H : Finset (Fin p × Fin l)) (k : ℕ) : Prop :=
  ∃ (R : Finset (Fin p)) (B : Finset (Fin l)), R.card + B.card ≤ k ∧
    ∀ i j, (i,j) ∈ H → i ∈ R ∨ j ∈ B

theorem triple_cross_cover {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E)
    {a c e : Fin p} {b d f : Fin l} (ac : a ≠ c) (ae : a ≠ e) (ce : c ≠ e)
    (bd : b ≠ d) (bf : b ≠ f) (df : d ≠ f)
    (ab : (a,b) ∈ F \ E) (cd : (c,d) ∈ F \ E) (ef : (e,f) ∈ F \ E) :
    smallCover (G \ E) 6 := by
  classical
  let row := fun (x y : Fin l) => univ.filter fun i : Fin p => (i,x) ∈ E ∧ (i,y) ∈ E
  let col := fun (x y : Fin p) => univ.filter fun j : Fin l => (x,j) ∈ E ∧ (y,j) ∈ E
  have hr (x y : Fin l) (ne : x ≠ y) : (row x y).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi k hk
    obtain ⟨_,hix,hiy⟩ := mem_filter.mp hi
    obtain ⟨_,hkx,hky⟩ := mem_filter.mp hk
    by_contra dik
    exact no4 i k x y dik ne ⟨hix,hiy,hkx,hky⟩
  have hc (x y : Fin p) (ne : x ≠ y) : (col x y).card ≤ 1 := by
    apply card_le_one.mpr
    intro j hj k hk
    obtain ⟨_,hxj,hyj⟩ := mem_filter.mp hj
    obtain ⟨_,hxk,hyk⟩ := mem_filter.mp hk
    by_contra djk
    exact no4 x y j k ne djk ⟨hxj,hxk,hyj,hyk⟩
  refine ⟨row b d ∪ row b f ∪ row d f,col a c ∪ col a e ∪ col c e,?_,?_⟩
  · have bound {α : Type} [DecidableEq α] (X Y Z : Finset α)
        (hx : X.card ≤ 1) (hy : Y.card ≤ 1) (hz : Z.card ≤ 1) :
        (X ∪ Y ∪ Z).card ≤ 3 := by
      have := card_union_le X Y
      have := card_union_le (X ∪ Y) Z
      omega
    exact Nat.add_le_add (bound _ _ _ (hr _ _ bd) (hr _ _ bf) (hr _ _ df))
      (bound _ _ _ (hc _ _ ac) (hc _ _ ae) (hc _ _ ce))
  · intro i j hij
    obtain ⟨pos,off⟩ := mem_sdiff.mp hij
    have h1 := cross a b i j (mem_sdiff.mp ab).1 (mem_sdiff.mp ab).2 pos off
    have h2 := cross c d i j (mem_sdiff.mp cd).1 (mem_sdiff.mp cd).2 pos off
    have h3 := cross e f i j (mem_sdiff.mp ef).1 (mem_sdiff.mp ef).2 pos off
    simp only [mem_union,row,col,mem_filter,mem_univ,true_and]
    tauto

-- Either two independent off-target pairs are maximal (their four
-- endpoints cover the relation), or a third disjoint pair can be chosen.
theorem sparse_operand {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E) :
    smallCover (F \ E) 4 ∨ smallCover (G \ E) 6 := by
  classical
  by_cases hex : ∃ a b, (a,b) ∈ F \ E
  · obtain ⟨a,b,ab⟩ := hex
    by_cases more : ∃ c d, (c,d) ∈ F \ E ∧ a ≠ c ∧ b ≠ d
    · obtain ⟨c,d,cd,ac,bd⟩ := more
      by_cases third : ∃ e f, (e,f) ∈ F \ E ∧ a ≠ e ∧ c ≠ e ∧ b ≠ f ∧ d ≠ f
      · obtain ⟨e,f,ef,ae,ce,bf,df⟩ := third
        exact Or.inr (triple_cross_cover _ _ _ no4 cross ac ae ce bd bf df ab cd ef)
      · left
        refine ⟨{a,c},{b,d},?_,?_⟩
        · simp [ac,bd]
        · intro i j hij
          simp only [mem_insert,mem_singleton]
          by_contra! h
          exact third ⟨i,j,hij,Ne.symm h.1.1,Ne.symm h.1.2,Ne.symm h.2.1,Ne.symm h.2.2⟩
    · left
      refine ⟨{a},{b},by simp,?_⟩
      intro i j hij
      simp only [mem_singleton]
      by_contra! h
      exact more ⟨i,j,hij,Ne.symm h.1,Ne.symm h.2⟩
  · left
    exact ⟨∅,∅,by simp,fun i j h => False.elim (hex ⟨i,j,h⟩)⟩

theorem sound_wire_sparse_operand {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    smallCover (footprint p l C u \ E) 4 ∨ smallCover (footprint p l C v \ E) 6 :=
  sparse_operand E _ _ no4 (sound_wire_cross E C hC u v sound)

-- Mask bit j records the colour of column j. Two row masks can coexist
-- only if they have at most one common one and at most one common zero.
def rowBit (x : Fin 32) (j : Fin 5) : Bool := x.val.testBit j.val
def encodeRow (m : Fin 5 → Bool) : Fin 32 :=
  ⟨(m 0).toNat + 2*(m 1).toNat + 4*(m 2).toNat + 8*(m 3).toNat + 16*(m 4).toNat,
   by have := (m 0).toNat_le; have := (m 1).toNat_le; have := (m 2).toNat_le
      have := (m 3).toNat_le; have := (m 4).toNat_le; omega⟩

theorem row_roundtrip (m : Fin 5 → Bool) (j : Fin 5) : rowBit (encodeRow m) j = m j := by
  fin_cases j <;> simp only [rowBit,encodeRow] <;>
    cases h0 : m 0 <;> cases h1 : m 1 <;> cases h2 : m 2 <;> cases h3 : m 3 <;> cases h4 : m 4 <;>
    first | exact h0.symm | exact h1.symm | exact h2.symm | exact h3.symm | exact h4.symm

def compatibleRows (x y : Fin 32) : Bool :=
  let a := x.val &&& y.val
  let b := (31-x.val) &&& (31-y.val)
  (a &&& (a-1) == 0) && (b &&& (b-1) == 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem compatible_iff : ∀ x y : Fin 32, compatibleRows x y = true ↔
    ∀ i j : Fin 5, i ≠ j → ¬ (rowBit x i = rowBit x j ∧ rowBit x j = rowBit y i ∧
        rowBit y i = rowBit y j) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem incompatible_five :
  ∀ x y : Fin 32, compatibleRows x y = true →
  ∀ z : Fin 32, compatibleRows x z = true → compatibleRows y z = true →
  ∀ u : Fin 32, compatibleRows x u = true → compatibleRows y u = true → compatibleRows z u = true →
  ∀ v : Fin 32, compatibleRows x v = true → compatibleRows y v = true → compatibleRows z v = true →
      compatibleRows u v = false := by decide +kernel

theorem monochrome_five (M : Fin 5 → Fin 5 → Bool) :
    ∃ i k j m, i ≠ k ∧ j ≠ m ∧ M i j = M i m ∧ M i m = M k j ∧ M k j = M k m := by
  by_contra! bad
  have h (i k : Fin 5) (ne : i ≠ k) :
      compatibleRows (encodeRow (M i)) (encodeRow (M k)) = true := by
    apply (compatible_iff _ _).mpr
    intro j m diff rect
    simp only [row_roundtrip] at rect
    exact bad i k j m ne diff rect.1 rect.2.1 rect.2.2
  have impossible := incompatible_five _ _ (h 0 1 (by decide)) _ (h 0 2 (by decide))
    (h 1 2 (by decide)) _ (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))
    _ (h 0 4 (by decide)) (h 1 4 (by decide)) (h 2 4 (by decide))
  simp [h 3 4 (by decide)] at impossible

-- A matching of five false-positive pairs on each operand would colour
-- a 5 by 5 grid by the direction of the forced target cross edge. Either
-- colour of monochromatic rectangle then violates four-freeness.
def hasFiveMatching {p l} (H : Finset (Fin p × Fin l)) : Prop :=
  ∃ (a : Fin 5 → Fin p) (b : Fin 5 → Fin l), Function.Injective a ∧ Function.Injective b ∧
    ∀ i, (a i,b i) ∈ H

theorem cross_matching_limit {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E) :
    ¬ (hasFiveMatching (F \ E) ∧ hasFiveMatching (G \ E)) := by
  classical
  rintro ⟨⟨a,b,ia,ib,ab⟩,⟨c,d,ic,id',cd⟩⟩
  let M (i j : Fin 5) := decide ((a i,d j) ∈ E)
  have red (i j) (h : M i j = true) : (a i,d j) ∈ E := of_decide_eq_true h
  have blue (i j) (h : M i j = false) : (c j,b i) ∈ E := by
    obtain ⟨hab,nab⟩ := mem_sdiff.mp (ab i)
    obtain ⟨hcd,ncd⟩ := mem_sdiff.mp (cd j)
    exact (cross _ _ _ _ hab nab hcd ncd).resolve_left (of_decide_eq_false h)
  obtain ⟨i,k,j,m,ik,jm,s,t,u⟩ := monochrome_five M
  cases h : M i j with
  | true =>
    exact no4 _ _ _ _ (ia.ne ik) (id'.ne jm)
      ⟨red i j h,red i m (s ▸ h),red k j (t ▸ s ▸ h),red k m (u ▸ t ▸ s ▸ h)⟩
  | false =>
    exact no4 _ _ _ _ (ic.ne jm) (ib.ne ik)
      ⟨blue i j h,blue k j (t ▸ s ▸ h),blue i m (s ▸ h),blue k m (u ▸ t ▸ s ▸ h)⟩

theorem sound_wire_matching_limit {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    ¬ (hasFiveMatching (footprint p l C u \ E) ∧ hasFiveMatching (footprint p l C v \ E)) :=
  cross_matching_limit E _ _ no4 (sound_wire_cross E C hC u v sound)

-- Hall's theorem with p-5 dummy line vertices. Unless four vertices
-- cover H, an injection from the p point vertices into augmented
-- neighbourhoods must use at least five distinct real line vertices.
theorem four_cover_of_no_five {p l} (H : Finset (Fin p × Fin l)) (none : ¬hasFiveMatching H) :
    smallCover H 4 := by
  classical
  by_contra noCover
  let N (i : Fin p) := univ.filter fun j : Fin l => (i,j) ∈ H
  have deficient (s : Finset (Fin p)) : 5 ≤ p - s.card + (s.biUnion N).card := by
    by_contra! small
    apply noCover
    refine ⟨univ \ s,s.biUnion N,?_,?_⟩
    · simpa [card_sdiff_of_subset (subset_univ s)] using (show _ ≤ 4 by omega : p - s.card + (s.biUnion N).card ≤ 4)
    · intro i j h
      by_cases hi : i ∈ s
      · exact Or.inr (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
      · exact Or.inl (by simpa using hi)
  have hp : 5 ≤ p := by simpa using deficient ∅
  let T (i : Fin p) := (N i).disjSum (univ : Finset (Fin (p-5)))
  have hall (s : Finset (Fin p)) : s.card ≤ (s.biUnion T).card := by
    rcases s.eq_empty_or_nonempty with rfl|⟨z,hz⟩
    · simp
    · have eq : s.biUnion T = (s.biUnion N).disjSum (univ : Finset (Fin (p-5))) := by
        ext v
        cases v with
        | inl j => simp [T]
        | inr d =>
          simp [T]
          exact ⟨z,hz⟩
      rw [eq,card_disjSum,card_univ,Fintype.card_fin]
      have := deficient s
      have hs : s.card ≤ p := by simpa using card_le_univ s
      omega
  obtain ⟨f,hf,member⟩ := (all_card_le_biUnion_card_iff_existsInjective' T).mp hall
  let U := univ.image f
  have size : U.card = p := by simp [U,card_image_of_injective _ hf]
  have cap : U.toRight.card ≤ p-5 := by simpa using card_le_univ U.toRight
  have split : U.toLeft.card + U.toRight.card = U.card := card_toLeft_add_card_toRight
  have five : 5 ≤ U.toLeft.card := by omega
  let b := U.toLeft.orderEmbOfCardLe five
  have pick (i : Fin 5) : ∃ a, f a = Sum.inl (b i) := by
    have hit := mem_toLeft.mp (U.toLeft.orderEmbOfCardLe_mem five i)
    obtain ⟨a,_,ha⟩ := mem_image.mp hit
    exact ⟨a,ha⟩
  choose a ha using pick
  apply none
  refine ⟨a,b,?_,b.injective,?_⟩
  · intro i j same
    exact b.injective (Sum.inl.inj ((ha i).symm.trans ((congrArg f same).trans (ha j))))
  · intro i
    have h := member (a i)
    rw [ha] at h
    exact (mem_filter.mp (inl_mem_disjSum.mp h)).2

theorem sound_wire_four_vertex_cover {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    smallCover (footprint p l C u \ E) 4 ∨ smallCover (footprint p l C v \ E) 4 := by
  by_cases h : hasFiveMatching (footprint p l C u \ E)
  · exact Or.inr (four_cover_of_no_five _ (fun hv => sound_wire_matching_limit E no4 C hC u v sound ⟨h,hv⟩))
  · exact Or.inl (four_cover_of_no_five _ h)

-- An exact nested AND for a matching. Each of its two children also accepts
-- one different off-diagonal edge. This rules out replacing every nested
-- AND by either child. The example satisfies the assigned gate restrictions.
def matchingReader : Circuit :=
  ⟨[⟨.and,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[4,5]⟩,
    ⟨.and,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[6,7]⟩,⟨.or,[6,8]⟩,⟨.and,[9,10]⟩],11⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem matchingReader_check :
    PEqualNP.TopForm.IsAO2 4 matchingReader ∧
    PEqualNP.TwoColour.tCount 4 matchingReader (fun i => decide (2 ≤ i)) = 0 ∧
    (∀ x : Fin 4 → Bool, circuitFun 4 matchingReader x =
      ((x 0 && x 2) || (x 1 && x 3))) ∧
    (∃ x : Fin 4 → Bool, (matchingReader.wires (List.ofFn x)).getD 9 false = true ∧
      circuitFun 4 matchingReader x = false) ∧
    (∃ x : Fin 4 → Bool, (matchingReader.wires (List.ofFn x)).getD 10 false = true ∧
      circuitFun 4 matchingReader x = false) := by decide +kernel

-- Even for graph-valued operands the one-row-plus-one-column bound is
-- sharp. The off-target pairs of the second operand include a matching of
-- size two, while the first contains an entire off-target 2 by 2 rectangle.
def twoStarEdges : Finset (Fin 4 × Fin 4) := {(0,2),(1,2),(2,0),(2,1)}
def gridOperand : Finset (Fin 4 × Fin 4) := twoStarEdges ∪ {(0,0),(0,1),(1,0),(1,1)}
def matchOperand : Finset (Fin 4 × Fin 4) := twoStarEdges ∪ {(3,2),(2,3)}

theorem two_vertex_bound_sharp :
    fourFree twoStarEdges ∧
    (∀ P L, (hits gridOperand P L ∧ hits matchOperand P L) ↔ hits twoStarEdges P L) ∧
    ¬fourFree (gridOperand \ twoStarEdges) ∧
    (∀ S : Finset (Fin 8),
      (∀ i j, (i,j) ∈ matchOperand \ twoStarEdges →
        Fin.castAdd 4 i ∈ S ∨ Fin.natAdd 4 j ∈ S) → 2 ≤ S.card) := by
  refine ⟨by unfold fourFree; decide +kernel,(nested_and_exact _ _ _).mpr (by decide +kernel),?_,?_⟩
  · intro clean
    exact clean 0 1 0 1 (by decide) (by decide) (by decide)
  · intro S covers
    have h := covers 3 2 (by decide)
    have k := covers 2 3 (by decide)
    by_contra! small
    have one := card_le_one.mp (show S.card ≤ 1 by omega)
    rcases h with h|h <;> rcases k with k|k <;>
      exact (by decide : _ ≠ _) (one _ h _ k)

-- Sharpness of the matching bound. Across the two sets of four pairs,
-- the target's first cross block is an 8-cycle. The other cross block is
-- its transposed bipartite complement, another 8-cycle.
def fourMatchE : Finset (Fin 8 × Fin 8) :=
  univ.filter fun e =>
    let i := e.1.val
    let j := e.2.val
    (i < 4 ∧ 4 ≤ j ∧ (j%4 = i ∨ j%4 = (i+1)%4)) ∨
    (4 ≤ i ∧ j < 4 ∧ i%4 ≠ j ∧ i%4 ≠ (j+1)%4)

def fourMatchF : Finset (Fin 8 × Fin 8) :=
  fourMatchE ∪ {(0,0),(1,1),(2,2),(3,3)}

def fourMatchG : Finset (Fin 8 × Fin 8) :=
  fourMatchE ∪ {(4,4),(5,5),(6,6),(7,7)}

theorem four_matching_sharp :
    fourFree fourMatchE ∧
    (∀ P L, (hits fourMatchF P L ∧ hits fourMatchG P L) ↔ hits fourMatchE P L) ∧
    (∃ a b : Fin 4 → Fin 8, Function.Injective a ∧ Function.Injective b ∧
      ∀ i, (a i,b i) ∈ fourMatchF \ fourMatchE) ∧
    (∃ c d : Fin 4 → Fin 8, Function.Injective c ∧ Function.Injective d ∧
      ∀ i, (c i,d i) ∈ fourMatchG \ fourMatchE) := by
  let a : Fin 4 → Fin 8 := Fin.castAdd 4
  let c : Fin 4 → Fin 8 := Fin.natAdd 4
  have ia : Function.Injective a := Fin.castAdd_injective _ _
  have ic : Function.Injective c := Fin.natAdd_injective _ _
  refine ⟨?_,(nested_and_exact _ _ _).mpr ?_,⟨a,a,ia,ia,?_⟩,⟨c,c,ic,ic,?_⟩⟩
  · unfold fourFree
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem matching_le_cover {p l m k} (H : Finset (Fin p × Fin l))
    (a : Fin m → Fin p) (b : Fin m → Fin l) (ia : Function.Injective a) (ib : Function.Injective b)
    (edges : ∀ i, (a i,b i) ∈ H) (cov : smallCover H k) : m ≤ k := by
  classical
  obtain ⟨R,B,cap,cover⟩ := cov
  let A := univ.filter fun i => a i ∈ R
  have hR : A.image a ⊆ R := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hi).2
  have hB : (univ \ A).image b ⊆ B := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    apply (cover _ _ (edges i)).resolve_left
    exact fun hr => (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,hr⟩)
  have r := card_le_card hR
  have d := card_le_card hB
  rw [card_image_of_injective _ ia] at r
  rw [card_image_of_injective _ ib,card_sdiff_of_subset (subset_univ A),card_univ,Fintype.card_fin] at d
  omega

theorem four_vertex_bound_sharp :
    ¬ smallCover (fourMatchF \ fourMatchE) 3 ∧ ¬ smallCover (fourMatchG \ fourMatchE) 3 := by
  obtain ⟨_,_,⟨a,b,ha,hb,left⟩,⟨c,d,hc,hd,right⟩⟩ := four_matching_sharp
  exact ⟨fun h => (by decide : ¬4 ≤ 3) (matching_le_cover _ _ _ ha hb left h),
    fun h => (by decide : ¬4 ≤ 3) (matching_le_cover _ _ _ hc hd right h)⟩

end PEqualNP.Research.StarNetworks

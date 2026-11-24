import Mathlib.Data.Finset.Sym
import PEqualNP.Defs
import Mathlib.Tactic
/-!
# Small matching number in a four-cycle-free bipartite graph

Removing the endpoints of a maximal matching leaves no edge. In either
periphery, charge one edge to each outside vertex and all remaining edges
to distinct unordered pairs of cover vertices. Four-cycle-freeness makes
the charge injective. The resulting quadratic error is within the allowed
square-root term whenever the maximum matching is small enough.

The circuit support and endpoint arguments are from the earlier L-meta-4675
research branch; they are included to make this module independently buildable.
-/
namespace PEqualNP.Research.SmallCover
open Finset
open scoped Sym2
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


-- Count edges outside a vertex cover. At each outside vertex keep one
-- neighbour free. Every other neighbour is charged to a pair of cover
-- vertices. A four-cycle would be needed to charge the same pair twice.
theorem periphery {U V : Type*} [DecidableEq U] [LinearOrder V] (D : Finset (U × V))
    (B : Finset V) (inside : ∀ e ∈ D, e.2 ∈ B)
    (thin : ∀ a c b d, (a,b) ∈ D → (a,d) ∈ D → (c,b) ∈ D → (c,d) ∈ D → b ≠ d → a=c) :
    D.card ≤ (D.image Prod.fst).card + B.card*(B.card-1)/2 := by
  classical
  let T := D.image Prod.fst
  let N := fun a => (D.filter fun e => e.1 = a).image Prod.snd
  have nei (a) (b) : b ∈ N a ↔ (a,b) ∈ D := by
    simp only [N,mem_image,mem_filter]
    constructor
    · rintro ⟨⟨i,j⟩,⟨h,rfl⟩,rfl⟩; exact h
    · intro h; exact ⟨(a,b),⟨h,rfl⟩,rfl⟩
  have nonempty (a) (ha : a ∈ T) : (N a).Nonempty := by
    obtain ⟨⟨i,j⟩,h,rfl⟩ := mem_image.mp ha
    exact ⟨j,(nei _ _).mpr h⟩
  let anchor := fun a (ha : a ∈ T) => (N a).min' (nonempty a ha)
  have anchorEdge (a) (ha : a ∈ T) : (a,anchor a ha) ∈ D :=
    (nei _ _).mp (min'_mem _ _)
  let code : (e : U × V) → e ∈ D → U ⊕ Sym2 V := fun e he =>
    if e.2 = anchor e.1 (mem_image_of_mem _ he) then .inl e.1
    else .inr s(anchor e.1 (mem_image_of_mem _ he),e.2)
  let pairs := B.sym2.filter (fun x => ¬x.IsDiag)
  have inject : ∀ x hx y hy, code x hx = code y hy → x=y := by
    rintro ⟨a,b⟩ hx ⟨c,d⟩ hy
    let ha : a ∈ T := mem_image_of_mem _ hx
    let hc : c ∈ T := mem_image_of_mem _ hy
    have h1 := anchorEdge a ha
    have h2 := anchorEdge c hc
    have lo1 : anchor a ha ≤ b := min'_le _ _ ((nei _ _).mpr hx)
    have lo2 : anchor c hc ≤ d := min'_le _ _ ((nei _ _).mpr hy)
    simp only [code]
    split <;> split
    · intro h; obtain rfl := Sum.inl.inj h; exact Prod.ext rfl (by solve_by_elim [Eq.trans,Eq.symm])
    · simp
    · simp
    · intro h; have eq := Sym2.eq_iff.mp (Sum.inr.inj h)
      rcases eq with ⟨e,rfl⟩|⟨e,f⟩
      · have r := thin _ _ _ _ h1 hx (e.symm ▸ h2) hy (Ne.symm (by assumption))
        exact Prod.ext r rfl
      · exfalso
        exact (by assumption : b ≠ anchor a ha) (le_antisymm (by simpa only [e,f] using lo2) lo1)
  have target (e) (he : e ∈ D) : code e he ∈ T.disjSum pairs := by
    rcases e with ⟨a,b⟩
    dsimp only [code]
    split
    · exact inl_mem_disjSum.mpr (mem_image_of_mem _ he)
    · apply inr_mem_disjSum.mpr
      apply mem_filter.mpr
      constructor
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨inside _ (anchorEdge a (mem_image_of_mem Prod.fst he)),inside _ he⟩
      · simpa only [Sym2.mk_isDiag_iff] using Ne.symm (by assumption : b ≠ _)
  have bound := card_le_card_of_injOn (s:=D.attach) (t:=T.disjSum pairs)
    (fun e => code e.val e.property) (fun e _ => target e.val e.property) (fun x hx y hy h => Subtype.ext (inject x.val x.property y.val y.property h))
  have num : pairs.card = B.card*(B.card-1)/2 := by
    rw [show pairs = B.sym2.filter (fun x => ¬x.IsDiag) from rfl]
    have diag : B.sym2.filter Sym2.IsDiag = B.image Sym2.diag := by
      ext z
      induction z using Sym2.inductionOn with
      | _ x y =>
        simp only [mem_filter,Finset.mk_mem_sym2_iff,Sym2.mk_isDiag_iff,mem_image]
        constructor
        · rintro ⟨h,rfl⟩; exact ⟨x,h.1,rfl⟩
        · rintro ⟨k,hk,he⟩
          rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨⟨hk,hk⟩,rfl⟩
    have total := card_filter_add_card_filter_not (s:=B.sym2) Sym2.IsDiag
    rw [diag,card_image_of_injective _ Sym2.diag_injective,card_sym2,Nat.choose_succ_succ] at total
    simp only [Nat.choose_one_right] at total
    change B.card + (B.sym2.filter (fun x => ¬x.IsDiag)).card = B.card + B.card.choose 2 at total
    rw [← Nat.choose_two_right]
    omega
  simpa only [Finset.card_attach,card_disjSum,num,T] using bound

theorem charge {p l : ℕ} (E M : Finset (Fin p × Fin l))
    (four : ∀ a c b d, a ≠ c → b ≠ d → ¬ ((a,b) ∈ E ∧ (a,d) ∈ E ∧ (c,b) ∈ E ∧ (c,d) ∈ E))
    (maximal : ∀ e ∈ E, e.1 ∈ M.image Prod.fst ∨ e.2 ∈ M.image Prod.snd) :
    E.card + M.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card + 2*M.card^2 := by
  classical
  let A := M.image Prod.fst
  let B := M.image Prod.snd
  let X := E.filter fun e => e.1 ∉ A
  let Y := E.filter fun e => e.2 ∉ B
  let Z := E.filter fun e => e.1 ∈ A ∧ e.2 ∈ B
  have hX : X ⊆ E := filter_subset _ _
  have hY : Y ⊆ E := filter_subset _ _
  have xb : ∀ e ∈ X, e.2 ∈ B := fun e h => (maximal e (hX h)).resolve_left (mem_filter.mp h).2
  have ya : ∀ e ∈ Y, e.1 ∈ A := fun e h => (maximal e (hY h)).resolve_right (mem_filter.mp h).2
  have thin (a c : Fin p) (b d : Fin l) (h1 : (a,b) ∈ E) (h2 : (a,d) ∈ E)
      (h3 : (c,b) ∈ E) (h4 : (c,d) ∈ E) (ne : b ≠ d) : a=c := by
    by_contra diff; exact four _ _ _ _ diff ne ⟨h1,h2,h3,h4⟩
  have lx := periphery X B xb (fun a c b d h1 h2 h3 h4 => thin a c b d (hX h1) (hX h2) (hX h3) (hX h4))
  let Y' := Y.image Prod.swap
  have swapmem (a : Fin p) (b : Fin l) : (b,a) ∈ Y' ↔ (a,b) ∈ Y := by
    constructor
    · intro h; obtain ⟨⟨i,j⟩,hij,eq⟩ := mem_image.mp h; cases eq; exact hij
    · intro h; exact mem_image.mpr ⟨(a,b),h,rfl⟩
  have ly := periphery Y' A (fun ⟨b,a⟩ h => ya _ ((swapmem _ _).mp h)) (by
    intro b d a c h1 h2 h3 h4 ne
    by_contra neq
    exact ne (thin a c b d (hY ((swapmem _ _).mp h1)) (hY ((swapmem _ _).mp h3))
      (hY ((swapmem _ _).mp h2)) (hY ((swapmem _ _).mp h4)) neq))
  have sy : Y'.card = Y.card := card_image_of_injective _ Prod.swap_injective
  have iy : Y'.image Prod.fst = Y.image Prod.snd := by simp [Y',image_image,Function.comp_def]
  rw [sy,iy] at ly
  have iz : Z ⊆ A ×ˢ B := fun e he => mem_product.mpr (mem_filter.mp he).2
  have z := card_le_card iz
  rw [card_product] at z
  have cover : E ⊆ X ∪ Y ∪ Z := by
    intro e he
    by_cases ha : e.1 ∈ A <;> by_cases hb : e.2 ∈ B <;> simp [X,Y,Z,he,ha,hb]
  have sum := (card_le_card cover).trans (card_union_le _ _)
  have mid := card_union_le X Y
  have px := card_le_card (image_subset_image (f:=Prod.fst) hX)
  have py := card_le_card (image_subset_image (f:=Prod.snd) hY)
  have ca : A.card ≤ M.card := card_image_le
  have cb : B.card ≤ M.card := card_image_le
  have ca2 := Nat.mul_le_mul ca (Nat.sub_le_sub_right ca 1)
  have cb2 := Nat.mul_le_mul cb (Nat.sub_le_sub_right cb 1)
  have ab := Nat.mul_le_mul ca cb
  cases e : M.card with
  | zero => simp_all; omega
  | succ k =>
    rw [e] at ca2 cb2 ab
    simp only [Nat.succ_sub_one] at ca2 cb2
    ring_nf at ab ca2 cb2 ⊢
    omega

end PEqualNP.Research.SmallCover

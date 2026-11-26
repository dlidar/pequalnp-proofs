import PEqualNP.Research.PlaneORDepth

namespace PEqualNP.Research.PlaneRuleDepth
open Finset PEqualNP.Research.PlaneORDepth

def below (x y : Input) := ∀ i, x i=true → y i=true
def pair (p l : Fin 21) : Input := fun i => decide (i=Fin.castAdd 21 p ∨ i=Fin.natAdd 21 l)
def independent (x : Input) := ∀ p l : Fin 21, adjacent p l=true →
  x (Fin.castAdd 21 p)=false ∨ x (Fin.natAdd 21 l)=false
def maximal (x : Input) := independent x ∧ ∀ y, independent y → below x y → y=x

theorem independent_iff (x : Input) : independent x ↔ graph x = false := by
  simp only [graph,decide_eq_false_iff_not,not_exists,not_and]
  unfold independent
  constructor
  · intro h p l a hp hl; rcases h p l a with k|k <;> simp_all
  · intro h p l a; by_cases hp : x (Fin.castAdd 21 p) = true
    · exact Or.inr (Bool.eq_false_iff.mpr (h p l a hp))
    · exact Or.inl (Bool.eq_false_iff.mpr hp)

theorem graph_mono (x y : Input) (b : below x y) (hit : graph x = true) : graph y = true := by
  obtain ⟨p,l,a,i,j⟩ := of_decide_eq_true hit
  exact decide_eq_true ⟨p,l,a,b _ i,b _ j⟩

theorem extremal_max : maximal extremal := by
  refine ⟨(independent_iff _).mpr extremal_zero,?_⟩
  intro y hy b
  funext i
  cases h : extremal i with
  | true => exact b i h
  | false =>
    apply Bool.eq_false_iff.mpr
    intro yy
    have m : below (flip i) y := by
      intro j h; rcases Bool.or_eq_true_iff.mp h with eq|on
      · have e : i=j := of_decide_eq_true eq; exact e ▸ yy
      · exact b j on
    have hit := graph_mono _ _ m (indispensable i h)
    rw [(independent_iff _).mp hy] at hit; cases hit

theorem posted_depth (f : Expr) (pos : ∀ p l, adjacent p l=true → eval (pair p l) f=true)
    (neg : ∀ x, maximal x → eval x f=false) : 6 ≤ depth f := by
  obtain ⟨S,n,z,k⟩ := certificate f extremal (neg _ extremal_max)
  have sub : holes ⊆ S := by
    intro i hi; by_contra hn
    have off := (mem_filter.mp hi).2
    obtain ⟨p,l,adj,hp,hl⟩ := of_decide_eq_true (indispensable i off)
    have bad := k (pair p l) (by
      intro j hj
      have ne : i≠j := fun e => hn (e ▸ hj)
      have dark : flip i j=false := by simp [PlaneORDepth.flip,ne,z j hj]
      apply Bool.eq_false_iff.mpr
      intro a
      rcases (of_decide_eq_true a : j=Fin.castAdd 21 p ∨ j=Fin.natAdd 21 l) with e|e <;>
        subst j <;> simp_all)
    rw [pos _ _ adj] at bad; cases bad
  have c := (card_le_card sub).trans n
  rw [holes_card] at c
  by_contra! h
  have u : 2^depth f ≤ 2^5 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

abbrev Rule := Finset ℕ × Finset ℕ
def andList : List Expr → Expr
  | [] => .lit true | f::fs => .conj f (andList fs)
noncomputable def operand (W : List Expr) (S : Finset ℕ) := andList (S.toList.map fun i => W.getD i (.lit false))
noncomputable def step (W : List Expr) (r : Rule) := W ++ [.disj (operand W r.1) (operand W r.2)]
def raw := List.ofFn (fun i : Bit => Expr.var i) ++ [.lit false]
noncomputable def output (rs : List Rule) (last : Finset ℕ) := operand (rs.foldl step raw) last

def valOp (w : List Bool) (s : Finset ℕ) := decide (∀ i∈s,w.getD i false=true)
def valStep (w : List Bool) (r : Rule) := w ++ [valOp w r.1 || valOp w r.2]
def valOut (rs : List Rule) (last : Finset ℕ) (x : Input) :=
  valOp (rs.foldl valStep (List.ofFn x ++ [false])) last

theorem eval_and (x : Input) (fs : List Expr) : eval x (andList fs)=true ↔ ∀ f∈fs,eval x f=true := by
  induction fs with
  | nil => simp [andList,eval]
  | cons f fs ih => simp [andList,eval,ih]

theorem eval_operand (x : Input) (W : List Expr) (S) :
    eval x (operand W S) = valOp (W.map (eval x)) S := by
  apply Bool.eq_iff_iff.mpr
  simp only [operand,eval_and,valOp,decide_eq_true_eq,List.mem_map,mem_toList,forall_exists_index,and_imp]
  constructor
  · intro h i hi
    have a := h _ i hi rfl
    cases e : W[i]? <;> simpa [List.getD_eq_getElem?_getD,e,eval] using a
  · intro h f i hi eq;subst f
    cases e : W[i]? <;> simpa [List.getD_eq_getElem?_getD,e,eval] using h i hi

theorem eval_rules (x : Input) (rs : List Rule) (W : List Expr) :
    (rs.foldl step W).map (eval x) = rs.foldl valStep (W.map (eval x)) := by
  induction rs generalizing W with
  | nil => rfl
  | cons r rs ih => simp [List.foldl_cons,ih,step,valStep,eval,eval_operand]

theorem eval_output (x : Input) (rs last) : eval x (output rs last)=valOut rs last x := by
  simp [output,valOut,eval_operand,eval_rules,raw,eval]

theorem posted_rules_lower (rs last) (pos : ∀ p l,adjacent p l=true → valOut rs last (pair p l)=true)
    (neg : ∀ x,maximal x → valOut rs last x=false) : 6 ≤ depth (output rs last) :=
  posted_depth _ (by simpa [eval_output] using pos) (by simpa [eval_output] using neg)

end PEqualNP.Research.PlaneRuleDepth

import PEqualNP.Research.L_meta_2584_minimal

namespace PEqualNP.Research.ReadTwoTerminal
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.TopForm
open PEqualNP.Research.ReadTwoBudget PEqualNP.Research.ReadTwoStates
open PEqualNP.Research.ReadTwoMinimal

/-- Accepted budget coordinates require the input to contain their support. -/
def Valid (p l : Bool) (f : State) (b : Bool) : Prop :=
  ∀ i j : Fin 3, (i.val = 0 ∨ p = true) → (j.val = 0 ∨ l = true) → f i j = true → b = true

theorem valid_mul {p l a b} {f g : State} (hf : Valid p l f a) (hg : Valid p l g b) :
    Valid p l (mul f g) (a && b) := by
  intro i j pi lj ok
  obtain ⟨u,v,x,y,h1,h2,hu,hx⟩ := of_decide_eq_true ok
  apply Bool.and_eq_true_iff.mpr
  exact ⟨hf u v (by rcases pi with h|h <;> first | right; exact h | left; omega)
    (by rcases lj with h|h <;> first | right; exact h | left; omega) hu,
    hg x y (by rcases pi with h|h <;> first | right; exact h | left; omega)
    (by rcases lj with h|h <;> first | right; exact h | left; omega) hx⟩

theorem valid_add {p l a b} {f g : State} (hf : Valid p l f a) (hg : Valid p l g b) :
    Valid p l (add f g) (a || b) := by
  intro i j h1 h2 yes
  apply Bool.or_eq_true_iff.mpr
  exact (Bool.or_eq_true_iff.mp yes).imp (hf i j h1 h2) (hg i j h1 h2)

theorem lookup {p l W V} (h : List.Forall₂ (Valid p l) W V) (o : ℕ) :
    Valid p l (W.getD o zero) (V.getD o false) := by
  induction h generalizing o with
  | nil => simp [Valid,zero]
  | cons h _ ih => cases o with
    | zero => exact h
    | succ o => exact ih o

theorem snoc {p l W V f b} (rel : List.Forall₂ (Valid p l) W V) (last : Valid p l f b) :
    List.Forall₂ (Valid p l) (W ++ [f]) (V ++ [b]) := by
  induction rel with
  | nil => exact .cons last .nil
  | cons h _ ih => exact .cons h ih

def pairInput (n a b : ℕ) (p l : Bool) := (List.range n).map fun i =>
  (decide (i = a) && p) || (decide (i = b) && l)

theorem leaf_valid (a b i : ℕ) (hab : a ≠ b) (p l : Bool) :
    Valid p l (encode (leafVectors [a,b] 2 i)) ((decide (i = a) && p) || (decide (i = b) && l)) := by
  intro u v hu hv yes
  by_cases ha : i = a
  · subst i
    simp [leafVectors,encode,fits,List.getD,hab,Ne.symm hab] at yes ⊢
    exact hu.resolve_left (by omega)
  · by_cases hb : i = b
    · subst i
      simp [leafVectors,encode,fits,List.getD,ha,hab] at yes ⊢
      exact hv.resolve_left (by omega)
    · simp [leafVectors,encode,ha,hb] at yes

theorem support (C : Circuit) (n a b : ℕ) (hab : a ≠ b) (hAO : IsAO2 n C)
    (p l : Bool) (o : ℕ) :
    Valid p l ((fastWires C n a b).getD o zero) ((C.wires (pairInput n a b p l)).getD o false) := by
  apply lookup
  let ev (V : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => V.getD i false))
  have fold (gs : List Gate) (ha : ∀ g ∈ gs, g.inputs.length = 2) (W V)
      (rel : List.Forall₂ (Valid p l) W V) :
      List.Forall₂ (Valid p l) (gs.foldl (fun w g => w ++ [fastStep w g]) W)
        (gs.foldl (fun v g => v ++ [ev v g]) V) := by
    induction gs generalizing W V with
    | nil => exact rel
    | cons g gs ih =>
      apply ih (fun g hg => ha _ (List.mem_cons_of_mem _ hg))
      apply snoc rel
      obtain ⟨a,b,eq⟩ := List.length_eq_two.mp (ha g (by simp))
      cases hop : g.op <;> simp only [fastStep,ev,hop,eq,List.map_cons,List.map_nil,
        List.getD_cons_zero,List.getD_cons_succ,GateOp.eval,List.any_cons,List.all_cons,
        List.any_nil,List.all_nil,Bool.and_true,Bool.or_false,id_eq] <;>
        first | exact valid_mul (lookup rel a) (lookup rel b)
              | exact valid_add (lookup rel a) (lookup rel b)
              | simp [Valid,zero]
  apply fold C.gates hAO.2.2
  unfold pairInput
  generalize List.range n = xs
  induction xs with
  | nil => exact .nil
  | cons i xs ih => exact .cons (leaf_valid a b i hab p l) ih

def edgeMasks : List ℕ := [0,256,288,384,416,432]
def AxisFree (f : State) : Prop := f 0 2 = false ∧ f 2 0 = false

theorem six_masks : ∀ m : Fin 512, Legal (bit m) ∧ AxisFree (bit m) ↔ m.val ∈ edgeMasks := by
  unfold AxisFree; decide +kernel

theorem exact_terminal (C : Circuit) (n a b : ℕ) (hab : a ≠ b) (hAO : IsAO2 n C)
    (hp : (C.wires (pairInput n a b true false)).getD C.output false = false)
    (hl : (C.wires (pairInput n a b false true)).getD C.output false = false) :
    (code ((fastWires C n a b).getD C.output zero)).val ∈ edgeMasks := by
  apply (six_masks _).mp
  rw [decode]
  refine ⟨fast_legal _ _ _ _ _, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro yes
    have e := support C n a b hab hAO false true C.output 0 2 (Or.inl rfl) (Or.inr rfl) yes
    exact Bool.noConfusion (hl.symm.trans e)
  · apply Bool.eq_false_iff.mpr
    intro yes
    have e := support C n a b hab hAO true false C.output 2 0 (Or.inr rfl) (Or.inl rfl) yes
    exact Bool.noConfusion (hp.symm.trans e)

def sample (k : Fin 6) : Circuit :=
  if k.val = 0 then ⟨[⟨.and,[0,1]⟩,⟨.and,[2,2]⟩,⟨.and,[3,2]⟩],4⟩
  else witness (edgeMasks.getD k.val 0)

def profile (k : Fin 6) (i j : Fin 3) := (edgeMasks.getD k.val 0).testBit (3*i.val+j.val)

/-- All six profiles are realized and distinguished even while each extension still computes AND. -/
theorem samples : ∀ (k : Fin 6) (i j : Fin 3),
    let C := test (sample k) i j
    IsAO2 2 C ∧ (∀ p l : Bool, (C.wires [p,l]).getD C.output false = (p && l)) ∧
    readsAtMost C 2 [0,1] 2 = profile k i j := by decide +kernel

theorem separated : ∀ k m : Fin 6, k ≠ m → ∃ i j, profile k i j ≠ profile m i j := by decide +kernel

theorem lower_exact {σ : Type} [Fintype σ] (summary : Circuit → σ) (step : Fin 2 → σ → σ)
    (accept : σ → Bool)
    (advance : ∀ (i : Fin 2) (C : Circuit), summary (spend i C) = step i (summary C))
    (sound : ∀ C : Circuit, IsAO2 2 C → (∀ p l : Bool, (C.wires [p,l]).getD C.output false = (p && l)) → accept (summary C) = readsAtMost C 2 [0,1] 2) :
    6 ≤ Fintype.card σ := by
  have inject : Function.Injective (fun k => summary (sample k)) := by
    intro k m eq
    by_contra ne
    obtain ⟨i,j,diff⟩ := separated k m ne
    have congr_test : summary (test (sample k) i j) = summary (test (sample m) i j) := by
      have iterate (b : Fin 2) (n : ℕ) (C D : Circuit) (he : summary C = summary D) :
          summary ((spend b)^[n] C) = summary ((spend b)^[n] D) := by
        induction n with
        | zero => exact he
        | succ n ih => simpa only [Function.iterate_succ_apply', advance, ih]
      exact iterate 0 _ _ _ (iterate 1 _ _ _ eq)
    have l := samples k i j
    have r := samples m i j
    apply diff
    rw [←l.2.2,←r.2.2,←sound _ l.1 l.2.1,←sound _ r.1 r.2.1,congr_test]
  simpa using Fintype.card_le_of_injective _ inject

end PEqualNP.Research.ReadTwoTerminal

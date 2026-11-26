import GridPacks
namespace PHPOverlap
open PEqualNP.ProofComplexity
abbrev Apart (a b : Grid → Bool) : Prop :=
  (∀ i : Fin 4, (∀ h : Fin 3, a (i,h) = false) → ∃ h : Fin 3, b (i,h) = true) ∧
  (∀ i j : Fin 4, ∀ h : Fin 3, i ≠ j → a (i,h) = true → a (j,h) = true →
       b (i,h) = false ∨ b (j,h) = false)
abbrev OddAt (f : Finset Grid) (a : Grid → Bool) : Prop := Odd ((f.filter (fun v => a v = true)).card)
def Witnesses (f : Finset Grid) (s : Bool) (n : Nat) : Prop :=
  ∃ a : Fin n → Grid → Bool, (∀ i, decide (OddAt f (a i)) = s) ∧ ∀ i j, i ≠ j → Apart (a i) (a j)
def Rich (f : Finset Grid) : Prop :=
  ∃ n k, 31 ≤ n+k ∧ Witnesses f false n ∧ Witnesses f true k
theorem from_pack {m s xs} (h : checkPack m s xs = true) :
    Witnesses (form m) s xs.length := by
  have ⟨ha,hd⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨fun i => assignment xs[i], fun i => beq_iff_eq.mp (List.all_eq_true.mp ha xs[i] (List.getElem_mem ..)),
    fun i j ne => of_decide_eq_true ((of_decide_eq_true hd) i j ne)⟩
def move (r : Fin 4 ≃ Fin 4) (c : Fin 3 ≃ Fin 3) := r.prodCongr c
theorem apart_move {a b : Grid → Bool} (h : Apart a b) (r : Fin 4 ≃ Fin 4) (c : Fin 3 ≃ Fin 3) :
    Apart (a ∘ move r c) (b ∘ move r c) := by
  constructor
  · intro i off
    obtain ⟨j,on⟩ := h.1 (r i) (fun j => by simpa [move] using off (c.symm j))
    exact ⟨c.symm j,by simpa [move] using on⟩
  · intro i j k ne ai aj
    exact h.2 (r i) (r j) (c k) (r.injective.ne ne) ai aj
theorem witness_move {f g : Finset Grid} {s n} (r : Fin 4 ≃ Fin 4) (c : Fin 3 ≃ Fin 3)
    (eq : f.map (move r c).toEmbedding = g) (h : Witnesses g s n) : Witnesses f s n := by
  obtain ⟨a,par,sep⟩ := h
  refine ⟨fun i => a i ∘ move r c,?_,fun i j ne => apart_move (sep i j ne) r c⟩
  intro i
  have hh : (f.filter (fun v => (a i ∘ move r c) v = true)).map (move r c).toEmbedding =
      g.filter (fun v => a i v = true) := by
    subst g
    rw [Finset.filter_map]
    rfl
  have hh' := congrArg Finset.card hh
  simp only [Finset.card_map] at hh'
  simpa only [OddAt,hh'] using par i
theorem rich_move {f g : Finset Grid} (r : Fin 4 ≃ Fin 4) (c : Fin 3 ≃ Fin 3)
    (eq : f.map (move r c).toEmbedding = g) (h : Rich g) : Rich f := by
  obtain ⟨n,k,lb,a,b⟩ := h
  exact ⟨n,k,lb,witness_move r c eq a,witness_move r c eq b⟩
end PHPOverlap

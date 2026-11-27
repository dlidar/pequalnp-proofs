import CloneLift
open PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Mask114591Support Mask114591Family
namespace Mask114591Permute

def wire {m : Nat} (n : Nat) (p : Fin m ≃ Fin m) (i : Nat) :=
  if h : n ≤ i ∧ i < n+m then n + (p ⟨i-n,by omega⟩).val else i

def rename {m : Nat} (n : Nat) (p : Fin m ≃ Fin m) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (wire n p)⟩

def circ {m : Nat} (n : Nat) (p : Fin m ≃ Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rename n p),wire n p C.output⟩

theorem fold_eval {m : Nat} (n : Nat) (p : Fin m ≃ Fin m) (gs : List Gate) (a b : List Bool)
    (h : n+m ≤ a.length) (len : b.length = a.length)
    (raw : ∀ i, b.getD (wire n p i) false = a.getD i false) :
    ∀ i, ((gs.map (rename n p)).foldl step b).getD (wire n p i) false =
      (gs.foldl step a).getD i false := by
  induction gs generalizing a b with
  | nil => exact raw
  | cons g gs ih =>
    apply ih
    · simp [step] <;> omega
    · simp [step,len]
    · intro i
      simp only [step,append_bit,rename,List.map_map]
      have ev : (g.inputs.map ((fun j => b.getD j false) ∘ wire n p)) =
          (g.inputs.map fun j => a.getD j false) := by
        apply List.map_congr_left
        intro j _
        exact raw j
      rw [ev]
      have he : wire n p i = b.length ↔ i = a.length := by
        simp only [wire]; split_ifs <;> omega
      simp only [he,raw]

theorem budget_perm {n m t : Nat} (p : Fin m ≃ Fin m) {A B : Fin n → Fin m → Bool}
    (he : ∀ u v, A u v = B u (p v)) (rep : RepSizeAtMost A t) : RepSizeAtMost B t := by
  obtain ⟨C,hc,sz,hr⟩ := rep
  refine ⟨circ n p C,?_,?_,?_⟩
  · intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    simpa [rename] using hc g' hg'
  · simpa [circ,Circuit.size] using sz
  · intro u v
    obtain ⟨v,rfl⟩ := p.surjective v
    rw [← he,← hr u v]
    apply fold_eval n p C.gates (oneEach u v) (oneEach u (p v)) (by simp [oneEach]) (by simp [oneEach])
    intro i
    rw [oneEach_bit,oneEach_bit]
    apply Bool.eq_iff_iff.mpr
    simp only [wire]
    split_ifs with hi
    · let j : Fin m := ⟨i-n,by omega⟩
      have hj : n + j.val = i := by dsimp [j];omega
      have hin : (p j).val = (p v).val ↔ j.val = v.val := by
        rw [← Fin.ext_iff,← Fin.ext_iff,Equiv.apply_eq_iff_eq]
      change decide (n + (p j).val = u.val ∨ n + (p j).val = n + (p v).val) = true ↔ _
      simp only [decide_eq_true_eq];omega
    · simp only [decide_eq_true_eq];omega

end Mask114591Permute
#print axioms Mask114591Permute.budget_perm

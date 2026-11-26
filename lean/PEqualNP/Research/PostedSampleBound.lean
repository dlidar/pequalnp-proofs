import PEqualNP.Research.SampleCount

namespace PEqualNP.Research.PostedSampleBound
open PEqualNP.Research.CapBoundary PEqualNP.Research.StarFormulas PEqualNP.Research.NecessarySamples
open PEqualNP.Research.FlagSamples PEqualNP.Research.NovelTrace

/-- Every witness to the posted existential needs at least 58 indexed samples. -/
theorem posted : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : ℕ) (x3 : Fin x2 → Finset (Fin (13 : ℕ))) (x4 : Fin x2 → Finset (Fin (13 : ℕ))) (x5 : Set (Fin x2)), ((∀ x6 ∈ x5, ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x3 x6 = {x8} ∧ x4 x6 = {x9}) ∧     (∀ x6 ∉ x5, (∀ x8 ∈ x3 x6, ∀ x10 ∈ x4 x6, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x3 x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x4 x6 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧       have x6 : Fin x2 → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x6 : Fin x2) (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x3 x6)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x4 x6)) x7;       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | x6 x8 x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         x8.length ≤ (63 : ℕ) →           (∀ (x10 : Fin x8.length),               have x11 : Set (Set (Fin x2)) := x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8};               x8.getD ↑x10 ∅ ∉ x11 ∧ ∃ x12 ∈ x11, ∃ x13 ∈ x11, x8.getD ↑x10 ∅ = x12 ∪ x13 ∨ x8.getD ↑x10 ∅ = x12 ∩ x13) →             x5 ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8}) → 58 ≤ x2 := by
  classical
  intro adj n P L labels h
  obtain ⟨yes,no,obstruct⟩ := h
  choose word hp hl using fun k => encode (P k) (L k)
  have rel : ∀ p l, inc p l ↔ adj p l := by decide +kernel
  apply PEqualNP.Research.SampleCount.sample_count word labels
  · let x : Fin n → Input → Bool := fun k i => Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P k)) (fun l => decide (l ∈ L k)) i
    let S : Set (Set (Fin n)) := {∅,Set.univ} ∪ Set.range (fun i : Input => {k | x k i=true})
    have wire (k : Fin n) (i : Input) : bits (word k) i = x k i := by
      refine @Fin.addCases 13 13 (fun i => bits (word k) i = x k i) ?_ ?_ i
      · intro p;apply Bool.eq_iff_iff.mpr
        change bits (word k) (point p)=true ↔ _
        rw [bits_point,hp]
        simp only [x,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
      · intro l;apply Bool.eq_iff_iff.mpr
        change bits (word k) (line l)=true ↔ _
        rw [bits_line,hl]
        simp only [x,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
    have seedEq : seeds word=S := by simp [seeds,S,wire]
    intro gs len good
    rw [seedEq] at *
    apply obstruct gs len
    intro j
    have step := good j.val j.isLt
    change gs[j.val] ∉ bank S (gs.take j.val) ∧ derived (bank S (gs.take j.val)) gs[j.val] at step
    simpa only [bank,derived,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,Option.getD_some] using step
  · intro k hk
    obtain ⟨p,l,e,sp,sl⟩ := yes k hk
    exact ⟨p,l,(rel p l).mpr e,(hp _).trans sp,(hl _).trans sl⟩
  · intro k hk
    obtain ⟨ind,pc,lc⟩ := no k hk
    unfold Generic;rw [hp,hl]
    exact ⟨fun p pm l lm e => ind p pm l lm ((rel p l).mp e),by simpa only [rel] using pc,
      by simpa only [rel] using lc⟩

end PEqualNP.Research.PostedSampleBound

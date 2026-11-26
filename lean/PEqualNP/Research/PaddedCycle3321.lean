import PEqualNP.Research.CycleNormal3321
namespace PEqualNP.Research.PaddedCycle3321
open Finset PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.Research.CycleNormal3321 PEqualNP.Research.ForestNormal3321

theorem padded_cycle {N p l : ℕ} (hn : 3 ≤ N) (left : Fin N ↪ Fin p) (right : Fin N ↪ Fin l)
    (C : Circuit) (fan : FanInTwo C) :
    let E := (edges N).image fun e => (left e.1,right e.2)
    (∀ z, circuitFun (p+l) C z = true ↔ Target E z) →
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ Below E D := by
  classical
  intro E ev
  letI : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  let undo : Fin (p+l) → Fin (N+N) := Fin.addCases
      (fun i => Fin.castAdd N (Function.invFun left i)) (fun j => Fin.natAdd N (Function.invFun right j))
  have undo_left (i) : undo (Fin.castAdd l (left i)) = Fin.castAdd N i := by
    simp [undo,Function.leftInverse_invFun left.injective i]
  have undo_right (j) : undo (Fin.natAdd p (right j)) = Fin.natAdd N j := by
    simp [undo,Function.leftInverse_invFun right.injective j]
  have transport (x : Fin (N+N) → Bool) : Target E (x ∘ undo) ↔ Target (edges N) x := by
    constructor
    · rintro ⟨p,l,h,a,b⟩
      obtain ⟨⟨i,j⟩,he,eq⟩ := mem_image.mp h
      cases eq
      exact ⟨i,j,he,by simpa only [Function.comp_apply,undo_left] using a,by simpa only [Function.comp_apply,undo_right] using b⟩
    · rintro ⟨i,j,he,a,b⟩
      exact ⟨left i,right j,mem_image.mpr ⟨(i,j),he,rfl⟩,by simpa only [Function.comp_apply,undo_left] using a,
         by simpa only [Function.comp_apply,undo_right] using b⟩
  have hc : HasCircuitSize (p+l) (circuitFun (p+l) C) C.size := ⟨C,fan,le_rfl,fun _ => rfl⟩
  obtain ⟨C',fan',bound,eval⟩ := Helpers.PermInputs.relabel_size undo _ _ hc
  have low := cycle_lower N hn C' fan' (fun z => by
    change C'.eval (List.ofFn z) = true ↔ _
    rw [eval];exact (ev _).trans (transport z))
  let P := (univ : Finset (Fin N)).image left
  have cov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ (∅ : Finset (Fin l)) := by
    rintro _ h
    obtain ⟨a,_,rfl⟩ := mem_image.mp h
    exact Or.inl (mem_image.mpr ⟨a.1,mem_univ _,rfl⟩)
  have pc : P.card ≤ N := by simpa [P] using card_image_le (s := (univ : Finset (Fin N))) (f := left)
  have ec : E.card ≤ (edges N).card := card_image_le
  have orig : (edges N).card ≤ N+N := by simpa [edges] using card_image_le (s := (univ : Finset (Fin (N+N)))) (f := edge)
  obtain ⟨D,ao,sz,ok,safe⟩ := compile_cover E P ∅ cov
  simp only [card_empty,Nat.add_zero] at sz
  exact ⟨D,ao,by omega,ok,safe⟩
end PEqualNP.Research.PaddedCycle3321

import Boundary
namespace Graph30863
open InverterRepair
def extendLabels (a : Fin 14 → Bool) (b : Fin 8 → Bool) (x : Point (Fin 8)) : Bool :=
  decide ((∃ i,a i=true ∧ p i≤x) ∨ (∃ j,b j=true ∧ n j≤x))
theorem extend_mono (a b) : Monotone (extendLabels a b) := by
  intro x y xy
  cases h : extendLabels a b x with
  | false => exact bot_le
  | true =>
    apply le_of_eq; symm; apply decide_eq_true
    rcases of_decide_eq_true h with ⟨i,ai,px⟩|⟨j,bj,nx⟩
    · exact Or.inl ⟨i,ai,px.trans xy⟩
    · exact Or.inr ⟨j,bj,nx.trans xy⟩
theorem on_positive (a b) (i : Fin 14) : extendLabels a b (p i)=a i := by
  apply Bool.eq_iff_iff.mpr
  simp only [extendLabels,decide_eq_true_eq]
  constructor
  · rintro (⟨j,h,ji⟩|⟨j,_,ji⟩)
    · exact anti_samples.1 j i ji ▸ h
    · exact False.elim ((anti_samples.2.2 i j).2 ji)
  · intro h;exact Or.inl ⟨i,h,le_rfl⟩
theorem on_negative (a b) (i : Fin 8) : extendLabels a b (n i)=b i := by
  apply Bool.eq_iff_iff.mpr
  simp only [extendLabels,decide_eq_true_eq]
  constructor
  · rintro (⟨j,_,ji⟩|⟨j,h,ji⟩)
    · exact False.elim ((anti_samples.2.2 j i).1 ji)
    · exact anti_samples.2.1 j i ji ▸ h
  · intro h;exact Or.inr ⟨i,h,le_rfl⟩
theorem universal_iff_tests (g b : Point (Fin 8) → Bool) (bm : Monotone b) :
    (∀ d : Point (Fin 8) → Bool → Bool, (∀ t,Monotone (fun x => d x t)) →
      (∀ x,Monotone (d x)) → (∀ x,d x (!(g x))=target x) → ∀ x,d x (b x)=target x) ↔
    (∀ i,g (p i)=false → b (p i)=true) ∧ (∀ j,g (n j)=true → b (n j)=false) := by
  rw [iff_boundary target_mono bm]
  constructor
  · rintro ⟨hp,hn⟩
    exact ⟨fun i => hp _ ((lower_iff _).mpr ⟨i,rfl⟩),fun j => hn _ ((upper_iff _).mpr ⟨j,rfl⟩)⟩
  · rintro ⟨hp,hn⟩
    constructor
    · intro x hx;obtain ⟨i,rfl⟩ := (lower_iff _).mp hx;exact hp i
    · intro x hx;obtain ⟨j,rfl⟩ := (upper_iff _).mp hx;exact hn j
end Graph30863

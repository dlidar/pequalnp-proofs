import AllTraces
namespace Graph30863
open InverterRepair PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def substitute : Circuit := ⟨[⟨.or,[1,2]⟩,
⟨.or,[5,6]⟩,
⟨.or,[0,8]⟩,
⟨.or,[3,9]⟩,
⟨.or,[10,11]⟩,
⟨.and,[1,4]⟩,
⟨.and,[3,6]⟩,
⟨.and,[10,11]⟩,
⟨.and,[12,7]⟩,
⟨.or,[13,14]⟩,
⟨.or,[17,15]⟩,
⟨.or,[18,16]⟩],19⟩
def monotoneReplacement (x : Point (Fin 8)) := ((x 1) ⊓ (x 4)) ⊔ ((x 3) ⊓ (x 6)) ⊔ ((x 0 ⊔ x 1 ⊔ x 2) ⊓ (x 3 ⊔ x 5 ⊔ x 6)) ⊔ ((x 0 ⊔ x 1 ⊔ x 2 ⊔ x 3 ⊔ x 5 ⊔ x 6) ⊓ (x 7))
theorem replace_size : substitute.size=12 := rfl
theorem substitute_eval : ∀ x : Point (Fin 8),substitute.eval (List.ofFn x)=monotoneReplacement x := by decide +kernel
theorem replacement_mono : Monotone monotoneReplacement := by
  intro x y hx;unfold monotoneReplacement
  repeat' apply sup_le_sup
  all_goals apply inf_le_inf
  all_goals repeat' apply sup_le_sup
  all_goals exact hx _
theorem twelve_repairs (d : Point (Fin 8) → Bool → Bool) (dx : ∀ t,Monotone (fun x => d x t)) (dt : ∀ x,Monotone (d x))
    (ok : ∀ x,d x (!(h x))=target x) : ∀ x,d x (substitute.eval (List.ofFn x))=target x := by
  have tb : (∀ i,h (p i)=false → monotoneReplacement (p i)=true) ∧ (∀ j,h (n j)=true → monotoneReplacement (n j)=false) := by decide +kernel
  intro x;rw [substitute_eval]
  exact (universal_iff_tests h monotoneReplacement replacement_mono).mpr tb d dx dt ok x
end Graph30863

import Boundary
namespace Graph30863
open InverterRepair
def del (i : Fin 8) (x : Point (Fin 8)) : Point (Fin 8) := fun j => if j=i then false else x j
theorem critical_pairs : ∀ i : Fin 8, ∃ a : Fin 14, ∃ b : Fin 8,
    h (p a)=false ∧ h (n b)=true ∧ del i (p a)≤n b := by decide +kernel
theorem forced_variables (v : Point (Fin 8) → Bool) (vm : Monotone v)
    (pos : ∀ i,h (p i)=false → v (p i)=true) (neg : ∀ j,h (n j)=true → v (n j)=false) :
    ∀ i : Fin 8,∃ x : Point (Fin 8),v (del i x)=false ∧ v x=true := by
  intro i
  obtain ⟨a,b,h1,h2,h3⟩ := critical_pairs i
  have le := vm h3
  rw [neg b h2] at le
  exact ⟨p a,le_antisymm le bot_le,pos a h1⟩
end Graph30863

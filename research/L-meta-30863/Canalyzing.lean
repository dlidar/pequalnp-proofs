import IsEssential
namespace Graph30863
open InverterRepair

theorem two_sided_raw_tests : ∀ j : Fin 8,
    (∃ i : Fin 14, h (p i) = false ∧ p i j = false) ∧
    (∃ i : Fin 8, h (n i) = true ∧ n i j = true) := by decide +kernel

theorem no_raw_absorption (v : Point (Fin 8) → Bool)
    (pos : ∀ i, h (p i) = false → v (p i) = true)
    (neg : ∀ i, h (n i) = true → v (n i) = false)
    (j : Fin 8) (z : Point (Fin 8) → Bool) :
    v ≠ (fun x => x j && z x) ∧ v ≠ (fun x => x j || z x) := by
  obtain ⟨⟨i, hi, hp⟩, ⟨k, hk, hn⟩⟩ := two_sided_raw_tests j
  constructor
  · intro eq
    have t := pos i hi
    simpa [eq, hp] using t
  · intro eq
    have t := neg k hk
    simpa [eq, hn] using t

end Graph30863

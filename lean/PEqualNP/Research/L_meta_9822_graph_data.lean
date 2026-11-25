import PEqualNP.Research.L_meta_9822_profiles
namespace PEqualNP.Research.GraphDistance
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PuncturedPetersen
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev Edge := Fin 45
abbrev Input := Fin 1024
abbrev Graph := Finset Edge
def ends (e : Edge) : Nat × Nat := ([(0, 1),(0, 2),(0, 3),(0, 4),(0, 5),(0, 6),(0, 7),(0, 8),(0, 9),(1, 2),(1, 3),(1, 4),(1, 5),(1, 6),(1, 7),(1, 8),(1, 9),(2, 3),(2, 4),(2, 5),(2, 6),(2, 7),(2, 8),(2, 9),(3, 4),(3, 5),(3, 6),(3, 7),(3, 8),(3, 9),(4, 5),(4, 6),(4, 7),(4, 8),(4, 9),(5, 6),(5, 7),(5, 8),(5, 9),(6, 7),(6, 8),(6, 9),(7, 8),(7, 9),(8, 9)] : List (Nat × Nat)).getD e.val (0,0)
def base : Graph := {3,4,9,13,21,24,28,34,36,37,40,41,43}
def five : Graph := {12,22,30,33,39,11,18,31,32}
def contained (e : Edge) (x : Input) : Bool := x.val.testBit (ends e).1 && x.val.testBit (ends e).2
def active (G : Graph) (x : Input) : Prop := ∃ e ∈ G, contained e x = true
instance (G : Graph) (x : Input) : Decidable (active G x) := inferInstanceAs (Decidable (∃ _ ∈ _, _))
def errors (G : Graph) := Finset.univ.filter fun x : Input => decide (active G x) != decide (active base x)
def added (e : Edge) := Finset.univ.filter fun x : Input => contained e x = true ∧ ¬ active base x
def lost (e : Edge) := Finset.univ.filter fun x : Input => active base x ∧ ¬ active (base.erase e) x
def alone (e : Edge) : Input := Fin.ofNat 1024 (2^(ends e).1 + 2^(ends e).2)

theorem isolated_pair : ∀ e f : Edge, contained f (alone e) = decide (e=f) := by decide +kernel
theorem alone_active (G : Graph) (e : Edge) : active G (alone e) ↔ e ∈ G := by simp [active,isolated_pair]
theorem original : ∀ x : Input, decide (active base x) = target x.val := by decide +kernel
theorem per_add : ∀ e : Edge, e ∉ base → 5 ≤ (added e).card ∧ ((added e).card=5 ↔ e ∈ five) := by decide +kernel
theorem per_deletion : ∀ e : Edge, e ∈ base → 9 ≤ (lost e).card := by decide +kernel

end PEqualNP.Research.GraphDistance

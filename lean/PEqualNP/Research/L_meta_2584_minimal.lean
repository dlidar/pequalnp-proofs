import PEqualNP.Research.L_meta_2584_states

namespace PEqualNP.Research.ReadTwoMinimal
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.TopForm
open PEqualNP.Research.ReadTwoBudget PEqualNP.Research.ReadTwoStates

/-- Append one AND of the current output with one of the original two inputs. -/
def spend (i : Fin 2) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨.and,[C.output,i.val]⟩], 2+C.size⟩

def test (C : Circuit) (i j : Fin 3) : Circuit :=
  ((spend 0)^[2-i.val]) (((spend 1)^[2-j.val]) C)

def representative (k : Fin 19) : Circuit := witness (masks.getD k.val 0)
def expected (k : Fin 19) (i j : Fin 3) : Bool := (masks.getD k.val 0).testBit (3*i.val+j.val)

theorem concrete_tests : ∀ (k : Fin 19) (i j : Fin 3),
    IsAO2 2 (test (representative k) i j) ∧
      readsAtMost (test (representative k) i j) 2 [0,1] 2 = expected k i j := by decide +kernel

theorem different_tests : ∀ k m : Fin 19, k ≠ m → ∃ i j, expected k i j ≠ expected m i j := by decide +kernel

/-- Any deterministic summary which can update for the two appended AND gates
and recover the joint read-2 decision on these legal circuits needs at least 19
values. The summary may depend on the entire prefix. -/
theorem lower_states {σ : Type} [Fintype σ] (summary : Circuit → σ) (step : Fin 2 → σ → σ)
    (accept : σ → Bool)
    (advance : ∀ (i : Fin 2) (C : Circuit), summary (spend i C) = step i (summary C))
    (sound : ∀ C : Circuit, IsAO2 2 C → accept (summary C) = readsAtMost C 2 [0,1] 2) :
    19 ≤ Fintype.card σ := by
  have inject : Function.Injective (fun k => summary (representative k)) := by
    intro k m eq
    by_contra ne
    obtain ⟨i,j,diff⟩ := different_tests k m ne
    have congr_test : summary (test (representative k) i j) = summary (test (representative m) i j) := by
      have iterate (b : Fin 2) (n : ℕ) (C D : Circuit) (he : summary C = summary D) :
          summary ((spend b)^[n] C) = summary ((spend b)^[n] D) := by
        induction n with
        | zero => exact he
        | succ n ih => simpa only [Function.iterate_succ_apply', advance, ih]
      exact iterate 0 _ _ _ (iterate 1 _ _ _ eq)
    have l := concrete_tests k i j
    have r := concrete_tests m i j
    apply diff
    rw [←l.2,←r.2,←sound _ l.1,←sound _ r.1,congr_test]
  simpa using Fintype.card_le_of_injective _ inject

#print axioms lower_states
end PEqualNP.Research.ReadTwoMinimal

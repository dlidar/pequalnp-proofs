import PEqualNP.Research.L_meta_2341_rows

namespace PEqualNP.Research.PuncturedFlags
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

def inputOn (m : ℕ) (bit : Bool) : List Bool :=
  ((List.ofFn fun i : Fin 13 => m.testBit i.val) ++
    List.ofFn fun i : Fin 13 => m.testBit (13+i.val)) ++ [bit]

def positiveInput (p l : Fin 13) (bit : Bool) : List Bool :=
  ((List.ofFn fun i : Fin 13 => decide (i=p)) ++
    List.ofFn fun i : Fin 13 => decide (i=l)) ++ [bit]

def negativeInput (Q : Finset (Fin 13)) (bit : Bool) : List Bool :=
  ((List.ofFn fun i : Fin 13 => decide (i∈Q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, ¬inc p l)) ++ [bit]

theorem flag_input : ∀ (p l : Fin 13) (bit : Bool), inputOn (edge p l) bit = positiveInput p l bit := by
  decide +kernel
theorem quad_input : ∀ (j : Fin 234) (bit : Bool), inputOn (neg j) bit = negativeInput (points (neg j)) bit := by
  decide +kernel
theorem recover_index : ∀ j : Fin 234, rowOf (mask (points (neg j))).val = j := by decide +kernel
theorem distinct_quadrangles : Function.Injective (fun j => points (neg j)) := by
  intro a b h
  have x := congrArg (fun Q => rowOf (mask Q).val) h
  simpa only [recover_index] using x

/-- Exact equality between the finite mask problem and the tests of L-meta-2341
with its puncture at (0,0), at either value of the extra input. -/
theorem tests_iff (C : Circuit) (bit : Bool) :
    ((∀ i, C.eval (inputOn (pos i) bit) = true) ∧ (∀ j, C.eval (inputOn (neg j) bit) = false)) ↔
    ((∀ p l : Fin 13, inc p l → p≠0 ∨ l≠0 → C.eval (positiveInput p l bit) = true) ∧
     (∀ Q, quad Q → C.eval (negativeInput Q bit) = false)) := by
  constructor
  · rintro ⟨hp,hn⟩
    constructor
    · intro p l incd other
      obtain ⟨i,e⟩ := (positive_rows p l).mpr ⟨incd,other⟩
      simpa only [e,flag_input] using hp i
    · intro Q hQ
      obtain ⟨j,e⟩ := table_complete Q hQ
      simpa only [quad_input,e] using hn j
  · rintro ⟨hp,hn⟩
    constructor
    · intro i
      obtain ⟨p,l,e⟩ := positive_shape i
      obtain ⟨a,b⟩ := (positive_rows p l).mp ⟨i,e⟩
      simpa only [e,flag_input] using hp p l a b
    · intro j
      simpa only [quad_input] using hn _ (negative_rows j).1

end PEqualNP.Research.PuncturedFlags

import Family
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Family Mask114591Support
namespace Mask114591Restrict

/-- Delete a block of zero input positions. Missing wires in the block become a permanently missing wire. -/
def wire (n k sentinel i : Nat) : Nat :=
  if i < n then i else if i < n+k then sentinel else i-k

def gate (n k sentinel : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire n k sentinel)⟩

def trim (n k : Nat) (C : Circuit) : Circuit :=
  let endWire := n + C.size
  ⟨C.gates.map (gate n k endWire),wire n k endWire C.output⟩

theorem fold_reads (n k sentinel : Nat) (gs : List Gate) (a b : List Bool)
    (init : n ≤ a.length) (space : a.length + gs.length ≤ sentinel)
    (len : b.length = a.length+k)
    (reads : ∀ i, a.getD (wire n k sentinel i) false = b.getD i false) :
    ∀ i, ((gs.map (gate n k sentinel)).foldl step a).getD (wire n k sentinel i) false =
      (gs.foldl step b).getD i false := by
  induction gs generalizing a b with
  | nil => exact reads
  | cons g gs ih =>
    apply ih
    · simp [step] <;> omega
    · simp only [step,List.length_append,List.length_singleton]; simp at space <;> omega
    · simp only [step,List.length_append,List.length_singleton] <;> omega
    · intro i
      simp only [step,append_bit,gate,List.map_map,Function.comp_apply]
      have ev : (g.inputs.map ((fun j => a.getD j false) ∘ wire n k sentinel)) =
          (g.inputs.map fun j => b.getD j false) := by
        apply List.map_congr_left
        intro j _
        exact reads j
      rw [ev]
      have he : wire n k sentinel i = a.length ↔ i = b.length := by
        simp only [wire]; split_ifs <;> simp at space <;> omega
      simp only [he,reads]

theorem trim_on (n k : Nat) (C : Circuit) (a b : List Bool)
    (la : a.length = n) (lb : b.length = n+k)
    (inputs : ∀ i, a.getD (wire n k (n+C.size) i) false = b.getD i false) :
    (trim n k C).eval a = C.eval b :=
  fold_reads n k _ C.gates a b (by omega) (by simp [la,Circuit.size]) (by omega) inputs C.output

theorem trim_fanin (n k : Nat) {C : Circuit} (hc : FanInTwo C) : FanInTwo (trim n k C) := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  simpa [gate] using hc g' hg'

theorem trim_mono (n k : Nat) {C : Circuit} (hc : Monotone2 C) : Monotone2 (trim n k C) := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  simpa [gate] using hc g' hg'

theorem trim_size (n k : Nat) (C : Circuit) : (trim n k C).size = C.size := by simp [trim,Circuit.size]

theorem trim_rep {n a k : Nat} {A : Fin n → Fin a → Bool} {B : Fin n → Fin (a+k) → Bool}
    {C : Circuit} (rep : Represents B C)
    (extend : ∀ u v, B u ⟨v.val,by omega⟩ = A u v) :
    Represents A (trim (n+a) k C) := by
  intro u v
  let w : Fin (a+k) := ⟨v.val,by omega⟩
  rw [trim_on (n+a) k C _ (oneEach u w) (by simp [oneEach] <;> omega) (by simp [oneEach] <;> omega)]
  · exact (rep u w).trans (extend u v)
  · intro i
    rw [oneEach_bit,oneEach_bit]
    apply Bool.eq_iff_iff.mpr
    simp only [wire,w,decide_eq_true_eq]
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega

end Mask114591Restrict
#print axioms Mask114591Restrict.trim_rep

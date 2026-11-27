import Ports
import IsEssential
namespace Graph30863
open InverterRepair PortSupport PEqualNP.CircuitLowerBounds

theorem shared_repair_lower (c : Circuit) (fan : ∀ g∈c.gates,g.inputs.length≤2)
    (vm : Monotone (fun x : Point (Fin 8) => c.eval (List.ofFn x)))
    (pos : ∀ i,h (p i)=false → c.eval (List.ofFn (p i))=true)
    (neg : ∀ i,h (n i)=true → c.eval (List.ofFn (n i))=false) :
    7≤c.size := by
  classical
  obtain ⟨s,sc,hs⟩ := rewind c.gates fan 8 {c.output}
  have incl : Finset.range 8 ⊆ s := by
    intro i hi
    have ilt := Finset.mem_range.mp hi
    let j : Fin 8 := ⟨i,ilt⟩
    by_contra no
    obtain ⟨x,h0,h1⟩ := forced_variables _ vm pos neg j
    have h := hs (List.ofFn (del j x)) (List.ofFn x) (by simp) (by simp) (by
      intro k hk
      have ne : k≠i := by intro e;exact no (e ▸ hk)
      by_cases kl : k<8
      · have neq : (⟨k,kl⟩ : Fin 8)≠j := fun e => ne (congrArg Fin.val e)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos kl, Option.getD_some]
        simp [del,neq]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,dif_neg kl])
    have eq := h c.output (by simp)
    change c.eval (List.ofFn (del j x))=c.eval (List.ofFn x) at eq
    rw [h0,h1] at eq
    contradiction
  have n := Finset.card_le_card incl
  simp at sc n; change 7≤c.gates.length; omega
end Graph30863

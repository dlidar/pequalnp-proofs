import PEqualNP.Research.PlaneRuleCost

namespace PEqualNP.Research.PlaneRuleWitness
open PEqualNP.Research.PlaneORDepth PEqualNP.Research.PlaneRuleDepth PEqualNP.Research.PlaneRuleCost

/-- Balanced OR of the complement of the selected eight-vertex maximal independent set. -/
def rules : List Rule := [
  ({0},{1}),
  ({2},{3}),
  ({4},{5}),
  ({6},{7}),
  ({9},{11}),
  ({12},{13}),
  ({14},{17}),
  ({18},{19}),
  ({20},{21}),
  ({22},{23}),
  ({25},{27}),
  ({28},{29}),
  ({30},{31}),
  ({32},{33}),
  ({34},{35}),
  ({36},{37}),
  ({38},{41}),
  ({43},{44}),
  ({45},{46}),
  ({47},{48}),
  ({49},{50}),
  ({51},{52}),
  ({53},{54}),
  ({55},{56}),
  ({57},{58}),
  ({60},{61}),
  ({62},{63}),
  ({64},{65}),
  ({66},{67}),
  ({68},{69}),
  ({70},{71}),
  ({72},{73}),
  ({74},{59})]
def finalWire : Finset ℕ := {75}

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
theorem thirty_three : rules.length = 33 := by decide +kernel
theorem all_backward : ∀ j : Fin rules.length, ∀ i∈rules[j.val].1 ∪ rules[j.val].2,i < 43+j.val := by decide +kernel
theorem final_backward : ∀ i∈finalWire,i<43+rules.length := by decide +kernel
theorem rejects_extremal : valOut rules finalWire extremal=false := by decide +kernel
private theorem row0 : ∀ l : Fin 21, adjacent 0 l=true → valOut rules finalWire (pair 0 l)=true := by decide +kernel
private theorem row1 : ∀ l : Fin 21, adjacent 1 l=true → valOut rules finalWire (pair 1 l)=true := by decide +kernel
private theorem row2 : ∀ l : Fin 21, adjacent 2 l=true → valOut rules finalWire (pair 2 l)=true := by decide +kernel
private theorem row3 : ∀ l : Fin 21, adjacent 3 l=true → valOut rules finalWire (pair 3 l)=true := by decide +kernel
private theorem row4 : ∀ l : Fin 21, adjacent 4 l=true → valOut rules finalWire (pair 4 l)=true := by decide +kernel
private theorem row5 : ∀ l : Fin 21, adjacent 5 l=true → valOut rules finalWire (pair 5 l)=true := by decide +kernel
private theorem row6 : ∀ l : Fin 21, adjacent 6 l=true → valOut rules finalWire (pair 6 l)=true := by decide +kernel
private theorem row7 : ∀ l : Fin 21, adjacent 7 l=true → valOut rules finalWire (pair 7 l)=true := by decide +kernel
private theorem row8 : ∀ l : Fin 21, adjacent 8 l=true → valOut rules finalWire (pair 8 l)=true := by decide +kernel
private theorem row9 : ∀ l : Fin 21, adjacent 9 l=true → valOut rules finalWire (pair 9 l)=true := by decide +kernel
private theorem row10 : ∀ l : Fin 21, adjacent 10 l=true → valOut rules finalWire (pair 10 l)=true := by decide +kernel
private theorem row11 : ∀ l : Fin 21, adjacent 11 l=true → valOut rules finalWire (pair 11 l)=true := by decide +kernel
private theorem row12 : ∀ l : Fin 21, adjacent 12 l=true → valOut rules finalWire (pair 12 l)=true := by decide +kernel
private theorem row13 : ∀ l : Fin 21, adjacent 13 l=true → valOut rules finalWire (pair 13 l)=true := by decide +kernel
private theorem row14 : ∀ l : Fin 21, adjacent 14 l=true → valOut rules finalWire (pair 14 l)=true := by decide +kernel
private theorem row15 : ∀ l : Fin 21, adjacent 15 l=true → valOut rules finalWire (pair 15 l)=true := by decide +kernel
private theorem row16 : ∀ l : Fin 21, adjacent 16 l=true → valOut rules finalWire (pair 16 l)=true := by decide +kernel
private theorem row17 : ∀ l : Fin 21, adjacent 17 l=true → valOut rules finalWire (pair 17 l)=true := by decide +kernel
private theorem row18 : ∀ l : Fin 21, adjacent 18 l=true → valOut rules finalWire (pair 18 l)=true := by decide +kernel
private theorem row19 : ∀ l : Fin 21, adjacent 19 l=true → valOut rules finalWire (pair 19 l)=true := by decide +kernel
private theorem row20 : ∀ l : Fin 21, adjacent 20 l=true → valOut rules finalWire (pair 20 l)=true := by decide +kernel
theorem accepts_edges : ∀ p l,adjacent p l=true → valOut rules finalWire (pair p l)=true := by
  intro p
  fin_cases p
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20

theorem sharp_on_one_negative : IsLeast {k : ℕ | ∃ (rs : List Rule) (last : Finset ℕ),
    rs.length=k ∧ (∀ p l,adjacent p l=true → valOut rs last (pair p l)=true) ∧
      valOut rs last extremal=false} 33 := by
  refine ⟨⟨rules,finalWire,thirty_three,accepts_edges,rejects_extremal⟩,?_⟩
  rintro k ⟨rs,last,rfl,yes,no⟩
  exact cost rs last yes no

end PEqualNP.Research.PlaneRuleWitness

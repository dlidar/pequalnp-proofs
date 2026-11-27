import Reference
namespace Graph32249
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def separated83 : Circuit := ⟨[⟨.or,[0,1]⟩,
⟨.and,[4,8]⟩,
⟨.or,[4,8]⟩,
⟨.or,[6,9]⟩,
⟨.or,[0,11]⟩,
⟨.and,[10,12]⟩,
⟨.and,[5,7]⟩,
⟨.or,[3,14]⟩,
⟨.or,[5,7]⟩,
⟨.or,[13,16]⟩,
⟨.and,[15,17]⟩,
⟨.or,[13,2]⟩,
⟨.or,[11,16]⟩,
⟨.and,[19,20]⟩,
⟨.or,[18,21]⟩], 22⟩
theorem size83 : separated83.size=15 := rfl
theorem monotone83 : ∀ g∈separated83.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g hg;simp only [separated83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
theorem correct83 : ∀ x : Fin 8 → Bool, separated83.eval (List.ofFn x)=target x := by decide +kernel
def separated86 : Circuit := ⟨[⟨.or,[2,4]⟩,
⟨.or,[4,6]⟩,
⟨.and,[6,8]⟩,
⟨.or,[1,10]⟩,
⟨.and,[0,3]⟩,
⟨.and,[5,7]⟩,
⟨.or,[7,12]⟩,
⟨.or,[5,14]⟩,
⟨.and,[3,15]⟩,
⟨.or,[13,16]⟩,
⟨.or,[0,17]⟩,
⟨.or,[11,18]⟩,
⟨.and,[9,19]⟩,
⟨.or,[2,18]⟩,
⟨.and,[15,21]⟩,
⟨.or,[20,22]⟩], 23⟩
theorem size86 : separated86.size=16 := rfl
theorem monotone86 : ∀ g∈separated86.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g hg;simp only [separated86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
theorem correct86 : ∀ x : Fin 8 → Bool, separated86.eval (List.ofFn x)=target x := by decide +kernel
end Graph32249

import Logic
import Branch0
import Branch1
import Branch2
import Branch3
import Branch4
import Branch5
import Branch6
import Branch7
import Branch8
import Branch9
import Branch10
import Branch11
import Branch12
import Branch13
import Branch14
import Branch15
import Branch16
import Branch17
import Branch18
import Branch19
import Branch20
import Branch21
import Branch22
import Branch23
import Branch24
import Branch25
import Branch26
import Branch27
import Branch28
import Branch29
import Branch30
import Branch31
import Branch32
import Branch33
import Branch34
import Branch35
namespace PEqualNP.Outside.Mask114591
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 16000 in
theorem denied_false : ∀ p ∈ denied, optimized 8 p.1 p.2 = false := by
  intro p h
  simp only [denied, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact br0
  · exact br1
  · exact br2
  · exact br3
  · exact br4
  · exact br5
  · exact br6
  · exact br7
  · exact br8
  · exact br9
  · exact br10
  · exact br11
  · exact br12
  · exact br13
  · exact br14
  · exact br15
  · exact br16
  · exact br17
  · exact br18
  · exact br19
  · exact br20
  · exact br21
  · exact br22
  · exact br23
  · exact br24
  · exact br25
  · exact br26
  · exact br27
  · exact br28
  · exact br29
  · exact br30
  · exact br31
  · exact br32
  · exact br33
  · exact br34
  · exact br35
end PEqualNP.Outside.Mask114591
theorem exact_negation : ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  rintro ⟨C,h,s,r⟩
  exact PEqualNP.Outside.Mask114591.no_small PEqualNP.Outside.Mask114591.denied_false C h s r
#print axioms exact_negation

import Traces
namespace Comparator9929.Tail
open Comparator9929.Trace
abbrev Old (x : Trace) := Within (falls x) (rises 112)
abbrev Pool (x : Trace) := Old x ∨ x = ~~~(76:Trace)
set_option maxHeartbeats 4000000 in
theorem must_combine_twice : ∀ a b : Trace, Pool a → Pool b →
    a ≠ 42 ∧ a &&& b ≠ 42 ∧ a ||| b ≠ 42 := by decide
#print axioms must_combine_twice
end Comparator9929.Tail

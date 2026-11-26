import CacheLower
import UsefulAll
import Strong0
import Strong1
import Strong2
import Strong3
import Strong4
import Strong5
import Strong6
import Strong7
import Strong8
import Strong9
import Strong10
import Strong11
namespace PEqualNP.Research.Cached9815
open TripleFormulaMass
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
private def allStrong : List Key := skeys0 ++ (skeys1 ++ (skeys2 ++ (skeys3 ++ (skeys4 ++ (skeys5 ++ (skeys6 ++ (skeys7 ++ (skeys8 ++ (skeys9 ++ (skeys10 ++ (skeys11 ++ (skeys12 ++ (skeys13 ++ (skeys14 ++ (skeys15 ++ (skeys16 ++ (skeys17 ++ (skeys18 ++ (skeys19 ++ (skeys20 ++ (skeys21 ++ (skeys22 ++ (skeys23 ++ (skeys24 ++ (skeys25 ++ (skeys26 ++ (skeys27 ++ (skeys28 ++ (skeys29 ++ (skeys30 ++ (skeys31 ++ (skeys32 ++ (skeys33 ++ (skeys34 ++ (skeys35 ++ (skeys36 ++ (skeys37 ++ (skeys38 ++ (skeys39 ++ (skeys40 ++ (skeys41 ++ (skeys42 ++ (skeys43 ++ (skeys44 ++ (skeys45 ++ (skeys46 ++ (skeys47 ++ (skeys48 ++ (skeys49 ++ (skeys50 ++ (skeys51 ++ (skeys52 ++ (skeys53 ++ (skeys54 ++ (skeys55 ++ (skeys56 ++ (skeys57 ++ (skeys58 ++ (skeys59 ++ (skeys60 ++ (skeys61 ++ (skeys62 ++ (skeys63 ++ (skeys64 ++ (skeys65 ++ (skeys66 ++ (skeys67 ++ (skeys68 ++ (skeys69 ++ (skeys70 ++ (skeys71 ++ (skeys72 ++ (skeys73 ++ (skeys74 ++ (skeys75)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem strong_on_other (k : Key) (notUse : usefulKey k=false) : Strong k := by
  have t : ∀ j : Key,usefulKey j=false → j∈allStrong := by decide +kernel
  have mem := t k notUse
  simp only [allStrong,List.mem_append] at mem
  rcases mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact strong0 k h
  · exact strong1 k h
  · exact strong2 k h
  · exact strong3 k h
  · exact strong4 k h
  · exact strong5 k h
  · exact strong6 k h
  · exact strong7 k h
  · exact strong8 k h
  · exact strong9 k h
  · exact strong10 k h
  · exact strong11 k h
  · exact strong12 k h
  · exact strong13 k h
  · exact strong14 k h
  · exact strong15 k h
  · exact strong16 k h
  · exact strong17 k h
  · exact strong18 k h
  · exact strong19 k h
  · exact strong20 k h
  · exact strong21 k h
  · exact strong22 k h
  · exact strong23 k h
  · exact strong24 k h
  · exact strong25 k h
  · exact strong26 k h
  · exact strong27 k h
  · exact strong28 k h
  · exact strong29 k h
  · exact strong30 k h
  · exact strong31 k h
  · exact strong32 k h
  · exact strong33 k h
  · exact strong34 k h
  · exact strong35 k h
  · exact strong36 k h
  · exact strong37 k h
  · exact strong38 k h
  · exact strong39 k h
  · exact strong40 k h
  · exact strong41 k h
  · exact strong42 k h
  · exact strong43 k h
  · exact strong44 k h
  · exact strong45 k h
  · exact strong46 k h
  · exact strong47 k h
  · exact strong48 k h
  · exact strong49 k h
  · exact strong50 k h
  · exact strong51 k h
  · exact strong52 k h
  · exact strong53 k h
  · exact strong54 k h
  · exact strong55 k h
  · exact strong56 k h
  · exact strong57 k h
  · exact strong58 k h
  · exact strong59 k h
  · exact strong60 k h
  · exact strong61 k h
  · exact strong62 k h
  · exact strong63 k h
  · exact strong64 k h
  · exact strong65 k h
  · exact strong66 k h
  · exact strong67 k h
  · exact strong68 k h
  · exact strong69 k h
  · exact strong70 k h
  · exact strong71 k h
  · exact strong72 k h
  · exact strong73 k h
  · exact strong74 k h
  · exact strong75 k h
theorem sharp_on_useful (k : Key) (use : usefulKey k=true) : Sharp k := by
  have t : ∀ j : Key,usefulKey j=true → j∈([92, 94, 95, 96, 104, 105, 106, 107, 108, 117, 119, 127, 128, 129, 137, 138, 146, 162, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180] : List Key) := by decide +kernel
  have m := t k use
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sharp92
  · exact sharp94
  · exact sharp95
  · exact sharp96
  · exact sharp104
  · exact sharp105
  · exact sharp106
  · exact sharp107
  · exact sharp108
  · exact sharp117
  · exact sharp119
  · exact sharp127
  · exact sharp128
  · exact sharp129
  · exact sharp137
  · exact sharp138
  · exact sharp146
  · exact sharp162
  · exact sharp164
  · exact sharp165
  · exact sharp166
  · exact sharp167
  · exact sharp168
  · exact sharp169
  · exact sharp171
  · exact sharp172
  · exact sharp173
  · exact sharp174
  · exact sharp175
  · exact sharp176
  · exact sharp177
  · exact sharp178
  · exact sharp179
  · exact sharp180
theorem useful_keys_count : ((List.finRange 182).filter usefulKey).length=34 := by decide +kernel
def liftRaw : Formula EdgeInput → Formula (Option EdgeInput)
  | .var i => .var (some i)
  | .conj a b => .conj (liftRaw a) (liftRaw b)
  | .disj a b => .disj (liftRaw a) (liftRaw b)
theorem lift_size (f) : (liftRaw f).leaves=f.leaves := by induction f <;> simp_all [liftRaw, Formula.leaves]
theorem lift_eval (k : Key) (f) (x) : (liftRaw f).eval (extendsKey k x)=f.eval x := by
  induction f <;> simp_all [liftRaw,Formula.eval,extendsKey,fill]
theorem exact_per_cache (k : Key) (s : Nat) : (∃ f : Formula (Option EdgeInput),
    f.leaves≤s ∧ ∀ x,f.eval (extendsKey k x)=target x) ↔ (if usefulKey k then 25 else 26)≤s := by
  cases h : usefulKey k with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    constructor
    · rintro ⟨f,le,correct⟩
      exact (strong_on_other k h f correct).trans le
    · intro le
      exact ⟨liftRaw formula,by rwa [lift_size,formula_size],fun x => (lift_eval _ _ _).trans (formula_correct x)⟩
  | true =>
    simp only [if_true]
    constructor
    · rintro ⟨f,le,correct⟩
      exact (every_key k f correct).trans le
    · intro le
      obtain ⟨f,e,correct⟩ := sharp_on_useful k h
      exact ⟨f,by rwa [e],correct⟩
end PEqualNP.Research.Cached9815

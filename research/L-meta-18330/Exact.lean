import Transport
import Upper
import Rep0
import Rep1
import Rep2
import Rep3
import Rep4
import Rep5

namespace PEqualNP.Research.Cached18330
open TripleFormulaMass
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem lowerAll (k : Key) : Bound (score k) k := by
  apply boundTransport
  generalize e : cls k = c
  fin_cases c
  · simpa [score,reprKey,e,keys] using rep0
  · simpa [score,reprKey,e,keys] using rep1
  · simpa [score,reprKey,e,keys] using rep2
  · simpa [score,reprKey,e,keys] using rep3
  · simpa [score,reprKey,e,keys] using rep4
  · simpa [score,reprKey,e,keys] using rep5

theorem inverseSignal (k : Key) (x : EdgeInput → Bool) :
    extendsKey k x ∘ Option.map (inv (sym k)) =
      extendsKey (reprKey k) (x ∘ inv (sym k)) := by
  have e := signalMap k (x ∘ inv (sym k))
  have cancel : (x ∘ inv (sym k)) ∘ perm (sym k) = x := by
    funext i; simp [Function.comp_def,(inputInverse _ _).2]
  rw [cancel] at e
  funext i
  cases i with
  | none => exact (congrFun e none).symm
  | some i => rfl

theorem upperAll (k : Key) : ∃ f : Formula (Option EdgeInput),
    f.leaves=score k ∧ ∀ x,f.eval (extendsKey k x)=target x := by
  by_cases h : cls k = 3
  · have key : reprKey k = 91 := by simp [reprKey,h,keys]
    refine ⟨rename (Option.map (inv (sym k))) pairOr,?_,?_⟩
    · simp [renameLeaves,pairOrSize,score,h]
    · intro x
      rw [renameEval,inverseSignal,key,pairOrEval]
      have e := sameTarget (sym k) (x ∘ inv (sym k))
      have cancel : (x ∘ inv (sym k)) ∘ perm (sym k) = x := by
        funext i; simp [Function.comp_def,(inputInverse _ _).2]
      rw [cancel] at e
      exact e.symm
  · exact ⟨ordinary,by simp [score,h,ordinarySize],ordinaryEval k⟩

theorem exactOneCache (k : Key) :
    (∃ f : Formula (Option EdgeInput), f.leaves=score k ∧ ∀ x,f.eval (extendsKey k x)=target x) ∧
    (∀ f : Formula (Option EdgeInput), (∀ x,f.eval (extendsKey k x)=target x) → score k ≤ f.leaves) :=
  ⟨upperAll k,lowerAll k⟩

theorem cacheProfile : ∀ k : Key, (score k = 27 ↔ 91 ≤ k.val ∧
    ((arg1 k).val < 7 ↔ (arg2 k).val < 7)) := by decide +kernel

theorem numberUseful : (Finset.univ.filter fun k : Key => score k = 27).card = 42 := by decide +kernel

end PEqualNP.Research.Cached18330

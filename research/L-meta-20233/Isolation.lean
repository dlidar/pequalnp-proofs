import SplitCore
namespace PlaneMask
abbrev Profile := (Fin 8 → Bool) × (Fin 8 → Bool)
def trimmed (r c : Byte) (x : Profile) : Profile :=
  (fun i => r.val.testBit i.val && x.1 i, fun i => c.val.testBit i.val && x.2 i)
theorem trim_mono (r c : Byte) : Monotone (trimmed r c) := by
  intro x y h
  constructor
  · intro i
    cases e : r.val.testBit i.val <;> simp [trimmed,e,h.1 i]
  · intro i
    cases e : c.val.testBit i.val <;> simp [trimmed,e,h.2 i]
def separate (r s : Byte) := ∀ i : Fin 8, r.val.testBit i.val = true → (rev s).val.testBit i.val = true
theorem trim_out {r c s t : Byte} (hr : separate r s) (hc : separate c t) (a : Cell) :
    trimmed r c (obs (rev s) (rev t) a) = obs r c a := by
  apply Prod.ext
  · funext i
    by_cases e : i.val = (a.val/8)
    · cases h : r.val.testBit i.val with
      | false => simp [trimmed,obs,send,← e,h]
      | true => simp [trimmed,obs,send,← e,h,hr i h]
    · simp [trimmed,obs,send,e]
  · funext i
    by_cases e : i.val = (a.val%8)
    · cases h : c.val.testBit i.val with
      | false => simp [trimmed,obs,send,← e,h]
      | true => simp [trimmed,obs,send,← e,h,hc i h]
    · simp [trimmed,obs,send,e]
def signals {ι : Type} (r c : ι → Byte) (enc : ι → Profile → Bool) (x : Cell) : ι → Bool :=
  fun j => enc j (obs (r j) (c j) x)
theorem isolate {ι : Type} [DecidableEq ι] (i : ι) (r c : ι → Byte)
    (enc : ι → Profile → Bool) (hm : ∀ j, Monotone (enc j))
    (raw : ∀ j, j ≠ i → separate (r j) (r i) ∧ separate (c j) (c i))
    (dec : (ι → Bool) → Prop) (hd : Monotone dec)
    (ok : ∀ x, dec (signals r c enc x) ↔ target x) : Fits (r i) (c i) := by
  apply (SplitMonotoneFactor.four_row_criterion _ _ _).mpr
  have force {a b : Cell} (h : SplitMonotoneFactor.Need (obs (rev (r i)) (rev (c i))) target a b) :
      signals r c enc a i = true ∧ signals r c enc b i = false := by
    have notle : ¬ signals r c enc a i ≤ signals r c enc b i := by
      intro hi
      apply h.2.1
      apply (ok b).mp
      apply hd _ ((ok a).mpr h.1)
      intro j
      by_cases hj : j = i
      · simpa [hj] using hi
      · obtain ⟨hr,hc⟩ := raw j hj
        apply hm j
        rw [← trim_out hr hc a,← trim_out hr hc b]
        exact trim_mono _ _ h.2.2
    cases ha : signals r c enc a i <;> cases hb : signals r c enc b i <;> simp_all
  intro a b u v hab huv hav
  have hz := hm i hav
  change signals r c enc a i ≤ signals r c enc v i at hz
  rw [(force hab).1,(force huv).2] at hz
  exact (by decide : ¬ true ≤ false) hz
end PlaneMask
#print axioms PlaneMask.isolate

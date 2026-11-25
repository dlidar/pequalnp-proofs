import PEqualNP.Research.L_meta_2341_data

namespace PEqualNP.Research.PuncturedFlags

/-- Boolean functions on point and line masks, evaluated at a fixed auxiliary bit. -/
abbrev Factor := ℕ → Bool
def Mon (f : Factor) : Prop := ∀ x y, sub x y = true → f x = true → f y = true
def Omits (f : Factor) (d : Fin 26) := ∀ z, f (extend d z) = f z
def Accepts (f : Factor) := ∀ i, f (pos i) = true
def Rejects (f : Factor) := ∀ j, f (neg j) = false

theorem sub_bits {u v : ℕ} : sub u v = true ↔ ∀ i, u.testBit i = true → v.testBit i = true := by
  unfold sub; rw [beq_iff_eq]
  constructor
  · intro eq i h
    have k := congrArg (fun z : ℕ => z.testBit i) eq
    simpa [Nat.testBit_and,h] using k
  · intro h; apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    cases e : u.testBit i with
    | false => simp
    | true => simp [h i e]

theorem project_mono (d : Fin 26) : Mon (project d) := by
  intro u v h yes
  obtain ⟨i,hi,ok⟩ := List.any_eq_true.mp yes
  apply List.any_eq_true.mpr
  refine ⟨i,hi,sub_bits.mpr ?_⟩
  intro k bit
  have z := sub_bits.mp ok k bit
  simp only [extend,Nat.testBit_or,Bool.or_eq_true] at z ⊢
  exact z.imp (sub_bits.mp h k) id

theorem project_omits (d : Fin 26) : Omits (project d) d := by
  intro z; simp [project,extend,Nat.or_assoc]

theorem project_accepts (d : Fin 26) : Accepts (project d) := by
  intro i
  apply List.any_eq_true.mpr
  exact ⟨i,List.mem_finRange i,sub_bits.mpr (fun k h => by simp [extend,Nat.testBit_or,h])⟩

/-- The projected positive DNF is the pointwise least monotone factor accepting
all flags and independent of input d. -/
theorem project_least {f : Factor} {d : Fin 26} (hm : Mon f) (hi : Omits f d) (hp : Accepts f) :
    ∀ z, project d z = true → f z = true := by
  intro z hz
  obtain ⟨i,_,he⟩ := List.any_eq_true.mp hz
  exact hi z ▸ hm _ _ he (hp i)

def product (fs : List (Fin 26 × Factor)) (z : ℕ) := fs.all (fun a => a.2 z)
def projected (ds : List (Fin 26)) (z : ℕ) := ds.all (fun d => project d z)

end PEqualNP.Research.PuncturedFlags

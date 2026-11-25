import Mathlib.Tactic
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# The center-to-endpoint cut of a disjoint union of four-vertex paths

Each path is left endpoint -- first center -- second center -- right endpoint.
A center pair set to 11 makes the output constant true. Otherwise each pair is
in one of three states (00, 10, 01), and any two such words can be distinguished
by turning on one external endpoint. This gives the exact minimum number of
states in any deterministic encoding of the center variables. Decoding may use
arbitrary Boolean computation and sharing.
-/
namespace PEqualNP.Research.PathCut

abbrev Bits (k : Nat) := Fin k → Bool × Bool
abbrev States (k : Nat) := Option (Fin k → Fin 3)

def hits {k} (x y : Bits k) : Prop :=
  ∃ i, ((x i).1 = true ∧ (x i).2 = true) ∨
    ((x i).1 = true ∧ (y i).1 = true) ∨ ((x i).2 = true ∧ (y i).2 = true)

def quiet {k} (w : Fin k → Fin 3) : Bits k :=
  fun i => (decide (w i = 1), decide (w i = 2))

def dense {k} : Bits k := fun _ => (true,true)
def zero {k} : Bits k := fun _ => (false,false)
def probe {k} (i : Fin k) (left : Bool) : Bits k :=
  fun j => (decide (j=i) && left, decide (j=i) && !left)

theorem quiet_hits {k} (w : Fin k → Fin 3) (y : Bits k) :
    hits (quiet w) y ↔ ∃ i, (w i = 1 ∧ (y i).1 = true) ∨ (w i = 2 ∧ (y i).2 = true) := by
  simp only [hits,quiet,decide_eq_true_eq]
  apply exists_congr
  intro i
  have diff : (1 : Fin 3) ≠ 2 := by decide
  aesop

theorem probe_left {k} (w : Fin k → Fin 3) (j : Fin k) :
    hits (quiet w) (probe j true) ↔ w j = 1 := by
  rw [quiet_hits]; simp [probe]

theorem probe_right {k} (w : Fin k → Fin 3) (j : Fin k) :
    hits (quiet w) (probe j false) ↔ w j = 2 := by
  rw [quiet_hits]; simp [probe]

def realize {k} : States k → Bits k
  | none => dense
  | some w => quiet w

theorem distinguish {k} (hk : 0 < k) (s t : States k)
    (h : ∀ y, hits (realize s) y ↔ hits (realize t) y) : s=t := by
  let j : Fin k := ⟨0,hk⟩
  have lit (y : Bits k) : hits dense y := ⟨j,Or.inl ⟨rfl,rfl⟩⟩
  have dark (w : Fin k → Fin 3) : ¬hits (quiet w) zero := by simp [quiet_hits,zero]
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some w => exact False.elim (dark w ((h zero).mp (lit zero)))
  | some v =>
    cases t with
    | none => exact False.elim (dark v ((h zero).mpr (lit zero)))
    | some w =>
      congr 1
      funext i
      have l := (probe_left v i).symm.trans ((h (probe i true)).trans (probe_left w i))
      have r := (probe_right v i).symm.trans ((h (probe i false)).trans (probe_right w i))
      generalize v i = a at *
      generalize w i = b at *
      fin_cases a <;> fin_cases b <;> simp_all

/-- Any correct encoder, even with unrestricted postprocessing, has at least
three to the k plus one different possible messages. -/
theorem encoding_lower {k} (hk : 0 < k) {M : Type*} [Fintype M]
    (enc : Bits k → M) (dec : M → Bits k → Prop)
    (correct : ∀ x y, hits x y ↔ dec (enc x) y) :
    3^k+1 ≤ Fintype.card M := by
  have inj : Function.Injective (fun s : States k => enc (realize s)) := by
    intro s t h
    apply distinguish hk s t
    intro y
    change enc (realize s) = enc (realize t) at h
    rw [correct,correct,h]
  simpa [States] using Fintype.card_le_of_injective _ inj

def state {k} (x : Bits k) : States k :=
  if ∃ i, (x i).1 = true ∧ (x i).2 = true then none
  else some (fun i => if (x i).1 then 1 else if (x i).2 then 2 else 0)

theorem state_correct {k} (x y : Bits k) :
    hits x y ↔ hits (realize (state x)) y := by
  unfold state
  split
  · rename_i h
    obtain ⟨i,h₁,h₂⟩ := h
    constructor
    · intro _; exact ⟨i,Or.inl ⟨rfl,rfl⟩⟩
    · intro _; exact ⟨i,Or.inl ⟨h₁,h₂⟩⟩
  · rename_i h
    change hits x y ↔ hits (quiet _) y
    rw [quiet_hits]
    apply exists_congr
    intro i
    have bad := not_exists.mp h i
    cases a : (x i).1 <;> cases b : (x i).2 <;> simp_all

theorem state_count (k : Nat) : Fintype.card (States k) = 3^k+1 := by simp [States]

theorem binary_cut {k b} (hk : 0 < k) (enc : Bits k → (Fin b → Bool))
    (dec : (Fin b → Bool) → Bits k → Prop)
    (correct : ∀ x y, hits x y ↔ dec (enc x) y) : 3^k+1 ≤ 2^b := by
  simpa using encoding_lower hk enc dec correct

/-- The encoder identifies exactly the pairs of centers that no choice of
outer endpoints can distinguish. -/
theorem state_eq_iff {k} (hk : 0 < k) (x z : Bits k) :
    state x = state z ↔ ∀ y, hits x y ↔ hits z y := by
  constructor
  · intro h y
    rw [state_correct x y,state_correct z y,h]
  · intro h
    apply distinguish hk
    intro y
    exact (state_correct x y).symm.trans ((h y).trans (state_correct z y))

theorem exact_binary_cut {k b} (hk : 0 < k) :
    (∃ (enc : Bits k → (Fin b → Bool)) (dec : (Fin b → Bool) → Bits k → Prop),
        ∀ x y, hits x y ↔ dec (enc x) y) ↔ 3^k+1 ≤ 2^b := by
  constructor
  · rintro ⟨enc,dec,h⟩
    exact binary_cut hk enc dec h
  · intro h
    classical
    have hc : Fintype.card (States k) ≤ Fintype.card (Fin b → Bool) := by
      simpa [state_count] using h
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
    refine ⟨fun x => e (state x), fun m y => hits (realize (Function.invFun e m)) y, ?_⟩
    intro x y
    change hits x y ↔ hits (realize (Function.invFun e (e (state x)))) y
    rw [Function.leftInverse_invFun e.injective]
    exact state_correct x y

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Vertices in the first copy of each part are centers, and the others endpoints.
The paths are indexed by j. -/
def pathEdges {k} (p l : Fin (k+k)) : Prop :=
  ∃ j : Fin k, (p = Fin.castAdd k j ∧ l = Fin.castAdd k j) ∨
                (p = Fin.castAdd k j ∧ l = Fin.natAdd k j) ∨
                (p = Fin.natAdd k j ∧ l = Fin.castAdd k j)

def assignment {k} (x y : Bits k) : Fin ((k+k)+(k+k)) → Bool :=
  Fin.addCases (Fin.addCases (fun i => (x i).1) (fun i => (y i).2))
               (Fin.addCases (fun i => (x i).2) (fun i => (y i).1))

theorem incidence_hits {k} (x y : Bits k) :
    (∃ p l, pathEdges p l ∧ assignment x y (Fin.castAdd (k+k) p) = true ∧
         assignment x y (Fin.natAdd (k+k) l) = true) ↔ hits x y := by
  constructor
  · rintro ⟨p,l,⟨j,pair⟩,hp,hl⟩
    use j
    rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl ⟨by simpa only [assignment,Fin.addCases_left] using hp,
        by simpa only [assignment,Fin.addCases_right,Fin.addCases_left] using hl⟩
    · exact Or.inr (Or.inl ⟨by simpa only [assignment,Fin.addCases_left] using hp,
        by simpa only [assignment,Fin.addCases_right] using hl⟩)
    · exact Or.inr (Or.inr ⟨by simpa only [assignment,Fin.addCases_right,Fin.addCases_left] using hl,
        by simpa only [assignment,Fin.addCases_right,Fin.addCases_left] using hp⟩)
  · rintro ⟨j,h|h|h⟩
    · refine ⟨_,_,⟨j,Or.inl ⟨rfl,rfl⟩⟩,?_⟩
      simpa only [assignment,Fin.addCases_left,Fin.addCases_right] using h
    · refine ⟨_,_,⟨j,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩,?_⟩
      simpa only [assignment,Fin.addCases_left,Fin.addCases_right] using h
    · refine ⟨_,_,⟨j,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩,?_⟩
      simpa only [assignment,Fin.addCases_left,Fin.addCases_right] using h.symm

/-- A circuit for the path incidence function with a one-way cut from all
centers to all endpoints must expose this many distinct binary messages. -/
theorem incidence_circuit_cut {k b} (hk : 0 < k) (C : Circuit)
    (computes : ∀ v, circuitFun ((k+k)+(k+k)) C v = true ↔ ∃ p l, pathEdges p l ∧
      v (Fin.castAdd (k+k) p) = true ∧ v (Fin.natAdd (k+k) l) = true)
    (enc : Bits k → (Fin b → Bool)) (dec : (Fin b → Bool) → Bits k → Bool)
    (cut : ∀ x y, circuitFun _ C (assignment x y) = dec (enc x) y) :
    3^k+1 ≤ 2^b := by
  apply binary_cut hk enc (fun m y => dec m y = true)
  intro x y
  rw [← cut,computes,incidence_hits]

private theorem apart {k} (a b : Fin k) : Fin.castAdd k a ≠ Fin.natAdd k b := by
  intro h
  have e := congrArg Fin.val h
  change a.val = k+b.val at e
  omega

private theorem parts {k} (a b : Fin k) :
    (pathEdges (Fin.castAdd k a) (Fin.castAdd k b) ↔ a=b) ∧
    (pathEdges (Fin.natAdd k a) (Fin.castAdd k b) ↔ a=b) ∧
    (pathEdges (Fin.castAdd k a) (Fin.natAdd k b) ↔ a=b) ∧
    ¬ pathEdges (Fin.natAdd k a) (Fin.natAdd k b) := by
  have rev (u v : Fin k) := (apart v u).symm
  have inj (u v : Fin k) : Fin.natAdd k u = Fin.natAdd k v ↔ u=v := by simp [Fin.ext_iff]
  simp only [pathEdges,Fin.castAdd_inj,apart,rev,inj,false_and,and_false,false_or,or_false]
  simp [eq_comm]

theorem pathEdges_square_free {k} (a c b d : Fin (k+k)) (ac : a ≠ c) (bd : b ≠ d)
    (ab : pathEdges a b) (ad : pathEdges a d) (cb : pathEdges c b) : ¬ pathEdges c d := by
  have h₁ := fun i j : Fin k => (parts i j).1
  have h₂ := fun i j : Fin k => (parts i j).2.1
  have h₃ := fun i j : Fin k => (parts i j).2.2.1
  have h₄ := fun i j : Fin k => (parts i j).2.2.2
  intro cd
  induction a using Fin.addCases <;> induction c using Fin.addCases <;>
    induction b using Fin.addCases <;> induction d using Fin.addCases <;>
    simp only [h₁,h₂,h₃,h₄] at * <;> grind

end PEqualNP.Research.PathCut

import Symmetry
import OneCertificate
import AdjacentStrongCertificate
import DisjointCertificate
namespace PEqualNP.Research.Triangle17393
open PEqualNP.Research.TripleFormulaMass
def pairLift (a b : Fin 10) (x : Fin 10 → Bool) (i : Fin 12) :=
  if h : i.val<10 then x ⟨i.val,h⟩ else if i.val=10 then !x a else !x b
def relabel (a b : Fin 10) (i : Fin 12) : Fin 12 :=
  if h : i.val<10 then (perm a b ⟨i.val,h⟩).castLE (by decide) else i
def duplicate (i : Fin 12) : Fin 11 := if h : i.val<10 then ⟨i.val,by omega⟩ else 10
theorem transform_pair (a b : Fin 10) (f : Formula (Fin 12))
    (ok : ∀ x,f.eval (pairLift a b x)=triangle x) (x : Fin 10 → Bool) :
    (rename (relabel a b) f).eval (pairLift 0 (rep a b) x)=triangle x := by
  rw [renamed_eval]
  have eq : (fun i => pairLift 0 (rep a b) x (relabel a b i)) =
      pairLift a b (fun i => x (perm a b i)) := by
    funext i
    by_cases h : i.val<10
    · simp [relabel,pairLift,h]
    · simp [relabel,pairLift,h,(coordinates a b).1,(coordinates a b).2.1]
  rw [eq,ok,perm_ok]
theorem duplicate_exact (g : Formula (Fin 12)) (ok : ∀ x,g.eval (pairLift 0 0 x)=triangle x) :
    24 ≤ g.leaves := by
  have h := One.lower (rename duplicate g) (by
    intro x
    rw [renamed_eval]
    have eq : (fun i => One.lift x (duplicate i)) = pairLift 0 0 x := by
      funext i
      by_cases h : i.val<10 <;> simp [duplicate,pairLift,One.lift,h]
    rw [eq,ok])
  simpa [renamed_leaves] using h
theorem pair_lower (a b : Fin 10) (f : Formula (Fin 12))
    (ok : ∀ x,f.eval (pairLift a b x)=triangle x) :
    (if rep a b=0 then 24 else if rep a b=1 then 24 else 23) ≤ f.leaves := by
  let g := rename (relabel a b) f
  have go (x) : g.eval (pairLift 0 (rep a b) x)=triangle x := transform_pair a b f ok x
  have eq : g.leaves=f.leaves := renamed_leaves _ _
  rcases (coordinates a b).2.2 with t|t|t
  · simp only [t,ite_true]
    rw [←eq];apply duplicate_exact;simpa [t] using go
  · rw [←eq];simp only [t];change 24≤g.leaves
    apply AdjacentStrong.lower g
    change ∀ x,g.eval (pairLift 0 1 x)=triangle x
    simpa only [t] using go
  · rw [←eq];simp only [t];change 23≤g.leaves
    apply Disjoint.lower g
    change ∀ x,g.eval (pairLift 0 7 x)=triangle x
    simpa only [t] using go
theorem two_raw_inverters_exclude_20 (a b : Fin 10) (f : Formula (Fin 12))
    (ok : ∀ x,f.eval (pairLift a b x)=triangle x) : 20 < 2+(f.leaves-1) := by
  have bound := pair_lower a b f ok
  split at bound
  · omega
  · split at bound <;> omega
theorem pair_upper (a b : Fin 10) : ∃ f : Formula (Fin 12), (∀ x,f.eval (pairLift a b x)=triangle x) ∧ f.leaves=24 := by
  let inc (i : Fin 10) : Fin 12 := i.castLE (by decide)
  refine ⟨rename inc witness,?_,(renamed_leaves _ _).trans witness_size⟩
  intro x
  rw [renamed_eval]
  have h : (fun i => pairLift a b x (inc i)) = x := by
    funext i; simp [pairLift,inc,i.isLt]
  rw [h,witness_eval,reference_correct]
theorem exact_same_or_adjacent (a b : Fin 10) (h : rep a b=0 ∨ rep a b=1) (k : Nat) :
    (∃ f : Formula (Fin 12), (∀ x,f.eval (pairLift a b x)=triangle x) ∧ f.leaves≤k) ↔ 24≤k := by
  constructor
  · rintro ⟨f,ok,le⟩
    have q := pair_lower a b f ok
    rcases h with e|e <;> simp [e] at q <;> omega
  · intro le
    obtain ⟨f,ok,eq⟩ := pair_upper a b
    exact ⟨f,ok,eq ▸ le⟩
end PEqualNP.Research.Triangle17393

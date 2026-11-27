import Necessity
import Reference
namespace Graph30863
open InverterRepair
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
def row (m : Nat) : Point (Fin 8) := fun i => m.testBit i.val
def p (i : Fin 14) := row ([9,18,33,34,36,65,68,72,129,130,132,136,160,192][i.val]!)
def n (i : Fin 8) := row ([7,14,21,28,56,66,112,144][i.val]!)
def h (x : Point (Fin 8)) := (x 0 && x 2) || (x 4 && (x 5 || x 7))
theorem samples : (∀ i,target (p i)=true) ∧ (∀ j,target (n j)=false) := by decide +kernel
theorem covers : ∀ x : Point (Fin 8), (target x=true → ∃ i,p i≤x) ∧ (target x=false → ∃ j,x≤n j) := by decide +kernel
theorem anti_samples : (∀ i j,p i≤p j → i=j) ∧ (∀ i j,n i≤n j → i=j) ∧
  (∀ i j,¬ p i≤n j ∧ ¬ n j≤p i) := by decide +kernel
theorem lower_iff (x : Point (Fin 8)) : Lower target x ↔ ∃ i,x=p i := by
  constructor
  · intro hx
    obtain ⟨i,le⟩ := (covers x).1 hx.1
    exact ⟨i,le.eq_or_lt.elim Eq.symm (fun lt => by have z := hx.2 _ lt; rw [samples.1] at z; contradiction)⟩
  · rintro ⟨i,rfl⟩
    refine ⟨samples.1 i,fun y lt => ?_⟩
    by_contra! hn
    obtain ⟨j,le⟩ := (covers y).1 (Bool.eq_true_of_not_eq_false hn)
    have ij := anti_samples.1 j i (le.trans lt.le)
    exact lt.not_ge (ij ▸ le)
theorem upper_iff (x : Point (Fin 8)) : Upper target x ↔ ∃ j,x=n j := by
  constructor
  · intro hx
    obtain ⟨j,le⟩ := (covers x).2 hx.1
    exact ⟨j,le.eq_or_lt.elim id (fun lt => by have z := hx.2 _ lt; rw [samples.2] at z; contradiction)⟩
  · rintro ⟨j,rfl⟩
    refine ⟨samples.2 j,fun y lt => ?_⟩
    by_contra! hn
    obtain ⟨i,le⟩ := (covers y).2 (Bool.eq_false_of_not_eq_true hn)
    have ij := anti_samples.2.1 j i (lt.le.trans le)
    exact lt.not_ge (ij.symm ▸ le)
theorem target_mono : Monotone target := by
  intro x y xy
  cases fx : target x with
  | false => exact bot_le
  | true =>
    cases fy : target y with
    | true => rfl
    | false =>
      obtain ⟨i,a⟩ := (covers x).1 fx
      obtain ⟨j,b⟩ := (covers y).2 fy
      exact False.elim ((anti_samples.2.2 i j).1 (a.trans (xy.trans b)))
theorem hardest_trace : (∀ i,h (p i)=false) ∧ (∀ j,h (n j)=decide (j.val ∈ ([0,2,4,6,7] : List Nat))) := by decide +kernel
end Graph30863

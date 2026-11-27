import Reference
import Universal
import Mathlib.Data.Fintype.Order
namespace Graph31116
open InverterRepair
abbrev Input := Fin 8 → Bool
def row (i : Fin 20) : Input := fun j => (([17, 18, 33, 36, 65, 66, 72, 96, 129, 130, 132, 144, 160, 192, 15, 28, 42, 56, 84, 136] : List Nat).getD i 0).testBit j
def edgeRow (i : Fin 14) : Input := row ⟨i.val, by omega⟩
def independentRow (i : Fin 6) : Input := row ⟨14+i.val,by omega⟩

def expr (x : Input) := (x 0 ⊓ x 4) ⊔ (x 1 ⊓ x 4) ⊔ (x 0 ⊓ x 5) ⊔ (x 2 ⊓ x 5) ⊔ (x 0 ⊓ x 6) ⊔ (x 1 ⊓ x 6) ⊔ (x 3 ⊓ x 6) ⊔ (x 5 ⊓ x 6) ⊔ (x 0 ⊓ x 7) ⊔ (x 1 ⊓ x 7) ⊔ (x 2 ⊓ x 7) ⊔ (x 4 ⊓ x 7) ⊔ (x 5 ⊓ x 7) ⊔ (x 6 ⊓ x 7)
theorem target_eq : ∀ x, target x = expr x := by decide +kernel
theorem target_mono : Monotone target := by
  intro x y xy; rw [target_eq,target_eq]; unfold expr
  repeat' apply sup_le_sup
  all_goals exact inf_le_inf (xy _) (xy _)

theorem rows_incomparable : ∀ i j : Fin 20, row i ≤ row j → i=j := by decide +kernel
theorem positive_rows : ∀ i, target (edgeRow i)=true := by decide +kernel
theorem negative_rows : ∀ i, target (independentRow i)=false := by decide +kernel
theorem positive_basis : ∀ x, target x=true → ∃ i, edgeRow i ≤ x := by decide +kernel
theorem negative_basis : ∀ x, target x=false → ∃ i, x ≤ independentRow i := by decide +kernel

def extension (t : Fin 20 → Bool) (x : Input) :=
  decide (∃ i, t i = true ∧ row i ≤ x)
theorem extension_mono (t) : Monotone (extension t) := by
  intro x y xy; cases e : extension t x
  · exact Bool.false_le _
  · have ha : ∃ i, t i=true ∧ row i ≤ x := of_decide_eq_true e
    obtain ⟨i,hi,le⟩ := ha
    have hb : extension t y=true := decide_eq_true ⟨i,hi,le.trans xy⟩
    rw [hb]
theorem extension_row (t) (j) : extension t (row j) = t j := by
  cases e : t j
  · apply decide_eq_false
    rintro ⟨i,hi,le⟩
    have eq := rows_incomparable i j le
    subst i; simp_all
  · exact decide_eq_true ⟨j,e,le_rfl⟩

theorem twenty_tests (h u : Input → Bool) (hh : Monotone h) (hu : Monotone u) :
    Universal target h u ↔
    (∀ i, h (edgeRow i)=false → u (edgeRow i)=true) ∧
    (∀ j, h (independentRow j)=true → u (independentRow j)=false) := by
  have k := boundary_iff target h u target_mono hh hu
    (fun x => ∃ i, edgeRow i=x) (fun x => ∃ i, independentRow i=x)
    (by rintro _ ⟨i,rfl⟩; exact positive_rows i)
    (by rintro _ ⟨j,rfl⟩; exact negative_rows j)
    (by intro x hx; obtain ⟨i,le⟩ := positive_basis x hx; exact ⟨_,⟨i,rfl⟩,le⟩)
    (by intro x hx; obtain ⟨j,le⟩ := negative_basis x hx; exact ⟨_,⟨j,rfl⟩,le⟩)
  rw [k]
  constructor
  · rintro ⟨p,n⟩; exact ⟨fun i => p _ ⟨i,rfl⟩,fun j => n _ ⟨j,rfl⟩⟩
  · rintro ⟨p,n⟩; constructor
    · rintro _ ⟨i,rfl⟩; exact p i
    · rintro _ ⟨j,rfl⟩; exact n j

theorem each_test_necessary (i : Fin 20) :
    ∃ h u : Input → Bool, Monotone h ∧ Monotone u ∧
      (∀ j, j≠i → u (row j) = target (row j)) ∧ ¬ Universal target h u := by
  let t := fun j : Fin 20 => if j=i then !(target (row j)) else target (row j)
  let g := extension t
  refine ⟨g,g,extension_mono _,extension_mono _,?_,?_⟩
  · intro j ne; simp [g,extension_row,t,ne]
  · intro good
    have flip : g (row i) = !(target (row i)) := by simp [g,extension_row,t]
    have mismatch : target (row i) ≠ g (row i) := by rw [flip]; cases target (row i) <;> decide
    exact mismatch (((universal_iff _ _ _ target_mono (extension_mono t)).mp good _ mismatch).symm)

end Graph31116

import Boundary
namespace Graph31116
open InverterRepair
def zeros : Input := fun _ => false
def ones : Input := fun _ => true
theorem endpoints : target zeros = false ∧ target ones = true := by decide +kernel
theorem final_and (h b : Input → Bool) (hm : Monotone h)
    (ok : ∀ x, (b x && !(h x))=target x) : ∀ x,b x=target x := by
  have t := ok ones
  rw [endpoints.2] at t
  have off : h ones=false := by cases e : h ones <;> simp_all
  intro x
  have le : x ≤ ones := fun _ => Bool.le_true _
  have eq := hm le; rw [off] at eq
  have hx := le_antisymm eq (Bool.false_le _)
  simpa [hx] using ok x
theorem final_or (h b : Input → Bool) (hm : Monotone h)
    (ok : ∀ x, (b x || !(h x))=target x) : ∀ x,b x=target x := by
  have t := ok zeros
  rw [endpoints.1] at t
  have on : h zeros=true := by cases e : h zeros <;> simp_all
  intro x
  have le : zeros ≤ x := fun _ => Bool.false_le _
  have eq := hm le; rw [on] at eq
  have hx := le_antisymm (Bool.le_true _) eq
  simpa [hx] using ok x
end Graph31116

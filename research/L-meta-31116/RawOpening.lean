import Boundary
namespace Graph31116

def replaceInput (useOr : Bool) (a b : Fin 8) (x : Input) : Input := fun j =>
  if j=b then (if useOr then x a || x b else x a && x b) else x j

theorem idem_replace (op : Bool) (a b : Fin 8) (x : Input) :
    replaceInput op a b (replaceInput op a b x)=replaceInput op a b x := by
  funext j; by_cases e : a=b <;> by_cases f : j=b <;> cases op <;> simp_all [replaceInput]

theorem arbitrary_decoder (op : Bool) (a b : Fin 8) :
    (∃ D : Input → Bool, ∀ x,D (replaceInput op a b x)=target x) ↔
      ∀ x,target (replaceInput op a b x)=target x := by
  constructor
  · rintro ⟨D,ok⟩ x
    rw [← ok (replaceInput op a b x),idem_replace,ok]
  · intro eq;exact ⟨target,eq⟩

def candidates (op : Bool) : List (Fin 8 × Fin 8) :=
  if op then [(0, 1), (0, 2), (0, 3), (1, 3), (5, 3), (6, 2), (6, 4), (7, 3)] else [(6, 3)]

theorem computed_list : ∀ op a b, a ≠ b →
    ((a,b) ∈ candidates op ↔ ∀ x,target (replaceInput op a b x)=target x) := by
  decide +kernel

theorem admissible_first_read (op : Bool) (a b : Fin 8) (distinct : a ≠ b) :
    (∃ D : Input → Bool, ∀ x,D (replaceInput op a b x)=target x) ↔ (a,b) ∈ candidates op :=
  (arbitrary_decoder op a b).trans (computed_list op a b distinct).symm

end Graph31116

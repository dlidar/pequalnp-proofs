import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
namespace WireMerge
-- The untouched wires can be represented by the proposition that one separates this row pair.
def bitSep (p n : Bool) : Prop := p = true ∧ n = false

theorem and_consume (p q n m : Bool) (rest : Prop)
    (old : rest ∨ bitSep p n ∨ bitSep q m) :
    (rest ∨ bitSep (p && q) (n && m)) ↔
      ((¬rest → bitSep p n → ¬bitSep q m → q=true) ∧
       (¬rest → bitSep q m → ¬bitSep p n → p=true)) := by
  by_cases r : rest <;> cases p <;> cases q <;> cases n <;> cases m <;> simp_all [bitSep]

theorem or_consume (p q n m : Bool) (rest : Prop)
    (old : rest ∨ bitSep p n ∨ bitSep q m) :
    (rest ∨ bitSep (p || q) (n || m)) ↔
      ((¬rest → bitSep p n → ¬bitSep q m → m=false) ∧
       (¬rest → bitSep q m → ¬bitSep p n → n=false)) := by
  by_cases r : rest <;> cases p <;> cases q <;> cases n <;> cases m <;> simp_all [bitSep]

theorem and_keep_right (p q n m : Bool) (rest : Prop)
    (old : rest ∨ bitSep p n ∨ bitSep q m) :
    (rest ∨ bitSep q m ∨ bitSep (p && q) (n && m)) ↔
      (¬rest → bitSep p n → ¬bitSep q m → q=true) := by
  by_cases r : rest <;> cases p <;> cases q <;> cases n <;> cases m <;> simp_all [bitSep]

theorem or_keep_right (p q n m : Bool) (rest : Prop)
    (old : rest ∨ bitSep p n ∨ bitSep q m) :
    (rest ∨ bitSep q m ∨ bitSep (p || q) (n || m)) ↔
      (¬rest → bitSep p n → ¬bitSep q m → m=false) := by
  by_cases r : rest <;> cases p <;> cases q <;> cases n <;> cases m <;> simp_all [bitSep]

end WireMerge

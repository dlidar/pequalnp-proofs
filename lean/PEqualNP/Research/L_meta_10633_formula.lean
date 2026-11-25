import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PEqualNP.Research.BinaryFormulaPanels

inductive Formula (α : Type*) where
  | leaf (i : α)
  | meet (u v : Formula α)
  | join (u v : Formula α)

def Formula.gates {α} : Formula α → Nat
  | .leaf _ => 0
  | .meet u v | .join u v => 1 + u.gates + v.gates

def Formula.value {α} : Formula α → (α → Bool) → Bool
  | .leaf i,x => x i
  | .meet u v,x => u.value x && v.value x
  | .join u v,x => u.value x || v.value x

variable {α β : Type*} [DecidableEq β] (row : β → α → Bool)

def Separates (t : Formula α) (p n : Finset β) :=
  (∀ i ∈ p, t.value (row i) = true) ∧ (∀ i ∈ n, t.value (row i) = false)

/-- A split chooses one child for each true row of an OR, or each false row of an AND. -/
inductive Partition (row : β → α → Bool) : Finset β → Finset β → Nat → Prop
  | leaf {p n} (i : α) (good : Separates row (.leaf i) p n) : Partition row p n 0
  | join {p n left a b} (ha : Partition row (p ∩ left) n a) (hb : Partition row (p \ left) n b) :
    Partition row p n (1+a+b)
  | meet {p n left a b} (ha : Partition row p (n ∩ left) a) (hb : Partition row p (n \ left) b) :
    Partition row p n (1+a+b)

theorem protocol_of_formula (t : Formula α) {p n : Finset β} (h : Separates row t p n) :
    Partition row p n t.gates := by
  induction t generalizing p n with
  | leaf i => exact .leaf i h
  | join u v hu hv =>
    let left := p.filter (fun i => u.value (row i) = true)
    apply Partition.join (left := left)
    · exact hu ⟨fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2,
        fun i hi => (Bool.or_eq_false_iff.mp (h.2 i hi)).1⟩
    · apply hv
      constructor
      · intro i hi
        obtain ⟨hp,hl⟩ := Finset.mem_sdiff.mp hi
        have val := Bool.or_eq_true_iff.mp (h.1 i hp)
        exact val.resolve_left (fun e => hl (Finset.mem_filter.mpr ⟨hp,e⟩))
      · exact fun i hi => (Bool.or_eq_false_iff.mp (h.2 i hi)).2
  | meet u v hu hv =>
    let left := n.filter (fun i => u.value (row i) = false)
    apply Partition.meet (left := left)
    · exact hu ⟨fun i hi => (Bool.and_eq_true_iff.mp (h.1 i hi)).1,
        fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2⟩
    · apply hv
      constructor
      · exact fun i hi => (Bool.and_eq_true_iff.mp (h.1 i hi)).2
      · intro i hi
        obtain ⟨hn,hl⟩ := Finset.mem_sdiff.mp hi
        have val := h.2 i hn
        change (u.value (row i) && v.value (row i)) = false at val
        have ne := fun e => hl (Finset.mem_filter.mpr ⟨hn,e⟩)
        cases a : u.value (row i) <;> simp_all

theorem formula_of_protocol {p n k} (h : Partition row p n k) :
    ∃ t, t.gates = k ∧ Separates row t p n := by
  induction h with
  | leaf i h => exact ⟨.leaf i,rfl,h⟩
  | @join p n l a b _ _ hl hr =>
    obtain ⟨u,rfl,hu⟩ := hl
    obtain ⟨v,rfl,hv⟩ := hr
    refine ⟨.join u v,rfl,?_,?_⟩
    · intro i hi
      by_cases m : i ∈ l
      · simp [Formula.value,hu.1 i (Finset.mem_inter.mpr ⟨hi,m⟩)]
      · simp [Formula.value,hv.1 i (Finset.mem_sdiff.mpr ⟨hi,m⟩)]
    · intro i hi
      simp [Formula.value,hu.2 i hi,hv.2 i hi]
  | @meet p n l a b _ _ hl hr =>
    obtain ⟨u,rfl,hu⟩ := hl
    obtain ⟨v,rfl,hv⟩ := hr
    refine ⟨.meet u v,rfl,?_,?_⟩
    · intro i hi
      simp [Formula.value,hu.1 i hi,hv.1 i hi]
    · intro i hi
      by_cases m : i ∈ l
      · simp [Formula.value,hu.2 i (Finset.mem_inter.mpr ⟨hi,m⟩)]
      · simp [Formula.value,hv.2 i (Finset.mem_sdiff.mpr ⟨hi,m⟩)]

theorem exact_cost {p n k} :
    Partition row p n k ↔ ∃ t, t.gates = k ∧ Separates row t p n := by
  constructor
  · exact formula_of_protocol row
  · rintro ⟨t,rfl,h⟩
    exact protocol_of_formula row t h

end PEqualNP.Research.BinaryFormulaPanels

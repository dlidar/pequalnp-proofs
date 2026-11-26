import PEqualNP.Research.NovelTrace

namespace PEqualNP.Research.FormulaTrace
open PEqualNP.Research.NovelTrace

inductive Formula (ι : Type) where
  | atom (i : ι) | bot | join (a b : Formula ι) | meet (a b : Formula ι)

def gates {ι} : Formula ι → ℕ
  | .atom _ | .bot => 0 | .join a b | .meet a b => gates a+gates b+1

def value {ι α} (raw : ι → Set α) : Formula ι → Set α
  | .atom i => raw i | .bot => ∅
  | .join a b => value raw a ∪ value raw b
  | .meet a b => value raw a ∩ value raw b

def truth {ι} (raw : ι → Bool) : Formula ι → Bool
  | .atom i => raw i | .bot => false
  | .join a b => truth raw a || truth raw b
  | .meet a b => truth raw a && truth raw b

theorem semantics {ι α} (bits : α → ι → Bool) (f : Formula ι) (r : α) :
    r ∈ value (fun i => {r | bits r i=true}) f ↔ truth (bits r) f=true := by
  induction f <;> simp_all [value,truth]

theorem available {α} (S : Set (Set α)) (xs ys : List (Set α)) : bank S xs ⊆ bank S (xs++ys) := by
  intro t h
  exact h.elim Or.inl (fun m => Or.inr (List.mem_append_left _ m))

theorem compile {ι α} (raw : ι → Set α) (S : Set (Set α)) (hr : ∀ i,raw i∈S) (empty : ∅∈S)
    (f : Formula ι) (xs : List (Set α)) (init : legal S xs) :
    ∃ ys : List (Set α), ys.length ≤ gates f ∧ legal S (xs++ys) ∧ value raw f ∈ bank S (xs++ys) := by
  classical
  induction f generalizing xs with
  | atom i => exact ⟨[],by simp,by simpa using init,Or.inl (hr i)⟩
  | bot => exact ⟨[],by simp,by simpa using init,Or.inl empty⟩
  | join a b l r | meet a b l r =>
    obtain ⟨ls,kl,lg,al⟩ := l xs init
    obtain ⟨rs,kr,rg,br⟩ := r (xs++ls) lg
    let B := bank S ((xs++ls)++rs)
    have ar := available S (xs++ls) rs al
    all_goals
      first
        | change ∃ ys, ys.length ≤ gates a+gates b+1 ∧ legal S (xs++ys) ∧ value raw a ∪ value raw b ∈ bank S (xs++ys)
        | change ∃ ys, ys.length ≤ gates a+gates b+1 ∧ legal S (xs++ys) ∧ value raw a ∩ value raw b ∈ bank S (xs++ys)
    all_goals
      first
        | apply Or.elim (em (value raw a ∪ value raw b ∈ B)) <;> intro hv
          · exact ⟨ls++rs,by simp;omega,by simpa [List.append_assoc] using rg,by simpa [B,List.append_assoc] using hv⟩
          · exact ⟨ls++rs++[value raw a ∪ value raw b],by simp;omega,
                by simpa [List.append_assoc] using snoc rg hv ⟨_,ar,_,br,Or.inl rfl⟩,
                Or.inr (by simp)⟩
        | apply Or.elim (em (value raw a ∩ value raw b ∈ B)) <;> intro hv
          · exact ⟨ls++rs,by simp;omega,by simpa [List.append_assoc] using rg,by simpa [B,List.append_assoc] using hv⟩
          · exact ⟨ls++rs++[value raw a ∩ value raw b],by simp;omega,
                by simpa [List.append_assoc] using snoc rg hv ⟨_,ar,_,br,Or.inr rfl⟩,
                Or.inr (by simp)⟩

def disjunction {ι} : List (Formula ι) → Formula ι
  | [] => .bot | [f] => f | f::g::gs => .join f (disjunction (g::gs))

theorem truth_or {ι} (raw : ι → Bool) (fs : List (Formula ι)) :
    truth raw (disjunction fs)=true ↔ ∃ f∈fs,truth raw f=true := by
  induction fs using disjunction.induct with
  | case1 => simp [disjunction,truth]
  | case2 => simp [disjunction]
  | case3 a b l ih => simp [disjunction,truth,ih]

end PEqualNP.Research.FormulaTrace

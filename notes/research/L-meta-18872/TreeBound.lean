import FormulaApplication
namespace PEqualNP.Research.TripleTree
open TripleFormulaMass TripleApplication SingleInverter IndependentTriple18872
inductive Tree (I : Type) where
  | input (i : I)
  | binary (conjunction : Bool) (f g : Tree I)
  | inv (f : Tree I)
def Tree.eval {I} (x : I → Bool) : Tree I → Bool
  | .input i => x i
  | .binary op f g => if op then f.eval x && g.eval x else f.eval x || g.eval x
  | .inv f => !(f.eval x)
def Tree.size {I} : Tree I → Nat
  | .input _ => 0
  | .binary _ f g => f.size+g.size+1
  | .inv f => f.size+1
def Tree.nots {I} : Tree I → Nat
  | .input _ => 0
  | .binary _ f g => f.nots+g.nots
  | .inv f => f.nots+1
def Tree.erase {I} : Tree I → Formula I
  | .input i => .var i
  | .binary true f g => .conj f.erase g.erase
  | .binary false f g => .disj f.erase g.erase
  | .inv f => f.erase
theorem erase_eval {I} (t : Tree I) (h : t.nots=0) (x : I → Bool) : t.erase.eval x=t.eval x := by
  induction t with
  | input => rfl
  | inv f ih => simp [Tree.nots] at h
  | binary op f g ih jh =>
    simp only [Tree.nots,Nat.add_eq_zero_iff] at h
    cases op <;> simp [Tree.erase,Tree.eval,Formula.eval,ih h.1,jh h.2]
theorem erase_size {I} (t : Tree I) : t.erase.leaves ≤ t.size+1 := by
  induction t with
  | input => rfl
  | inv f ih => simp [Tree.erase,Tree.size];omega
  | binary op f g ih jh => cases op <;> simp [Tree.erase,Tree.size,Formula.leaves] <;> omega
theorem monotone_formula {n} (f : Formula (Fin n)) (x y : Signal n) (h : Extends x y) :
    f.eval x=true → f.eval y=true := by
  induction f with
  | var i => exact h i
  | conj f g a b => simp only [Formula.eval,Bool.and_eq_true_iff]; rintro ⟨u,v⟩; exact ⟨a u,b v⟩
  | disj f g a b => simp only [Formula.eval,Bool.or_eq_true_iff]; exact Or.imp a b

/-- The other input of an AND with a true minimum endpoint is identically true
    when it is monotone. Dually, an OR with a false maximum endpoint has an
    identically false monotone input. -/
theorem simplify_side {n} (op : Bool) (a b : Tree (Fin n)) (h : b.nots=0)
    (lo : (Tree.binary op a b).eval (fun _ => false)=true)
    (hi : (Tree.binary op a b).eval (fun _ => true)=false) :
    ∀ x,(Tree.binary op a b).eval x=a.eval x := by
  have mono (x y : Signal n) (le : Extends x y) : b.eval x=true → b.eval y=true := by
    rw [← erase_eval b h,← erase_eval b h]
    exact monotone_formula _ _ _ le
  intro x
  cases op
  · have m := (Bool.or_eq_false_iff.mp hi).2
    have z : b.eval x=false := by
      cases t : b.eval x with
      | false => rfl
      | true =>
        have hit := mono x (fun _ => true) (fun _ _ => rfl) t
        rw [m] at hit
        contradiction
    simp [Tree.eval,z]
  · have m := (Bool.and_eq_true_iff.mp lo).2
    have z := mono (fun _ => false) x (by intro i a;contradiction) m
    simp [Tree.eval,z]

theorem swap_eval {I} (op : Bool) (a b : Tree I) (x : I → Bool) :
    (Tree.binary op a b).eval x=(Tree.binary op b a).eval x := by
  cases op <;> simp [Tree.eval,Bool.and_comm,Bool.or_comm]

theorem extract {n} (t : Tree (Fin n)) (few : t.nots ≤ 1)
    (lo : t.eval (fun _ => false)=true) (hi : t.eval (fun _ => true)=false) :
    ∃ f : Formula (Fin n), f.leaves ≤ t.size ∧ ∀ x,t.eval x= !(f.eval x) := by
  induction t with
  | input i => contradiction
  | inv t ih =>
    have z : t.nots=0 := by simp [Tree.nots] at few;omega
    exact ⟨t.erase,erase_size _,fun x => by rw [erase_eval _ z];rfl⟩
  | binary op a b ih jh =>
    simp only [Tree.nots] at few
    by_cases z : b.nots=0
    · have eq := simplify_side op a b z lo hi
      obtain ⟨f,le,h⟩ := ih (by omega) ((eq _).symm.trans lo) ((eq _).symm.trans hi)
      exact ⟨f,by simp [Tree.size];omega,fun x => (eq x).trans (h x)⟩
    · have eq := simplify_side op b a (by omega) ((swap_eval _ _ _ _).symm.trans lo) ((swap_eval _ _ _ _).symm.trans hi)
      have same (x) := (swap_eval op a b x).trans (eq x)
      obtain ⟨f,le,h⟩ := jh (by omega) ((same _).symm.trans lo) ((same _).symm.trans hi)
      exact ⟨f,by simp [Tree.size];omega,fun x => (same x).trans (h x)⟩

theorem target_tree_bound (t : Tree (Fin 15)) (few : t.nots ≤ 1)
    (exact_on : ∀ x,t.eval x=target x) : 44 ≤ t.size := by
  obtain ⟨f,le,eq⟩ := extract t few ((exact_on _).trans (by decide)) ((exact_on _).trans (by decide))
  apply le_trans _ le
  exact inverted_formula_lower f (fun _ b => b) (fun _ _ _ _ _ h => h)
    (fun x => (eq x).symm.trans (exact_on x))
end PEqualNP.Research.TripleTree

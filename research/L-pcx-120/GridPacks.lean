import Overlap
namespace PHPOverlap
open PEqualNP.ProofComplexity
abbrev Grid := Fin 4 × Fin 3
abbrev F := linOfClause '' PHP 4 3
def assignment (x : Nat) (v : Grid) := x.testBit (3*v.1.val+v.2.val)
def form (m : Nat) : Finset Grid := Finset.univ.filter (fun v => assignment m v = true)
def parity (m x : Nat) : Bool := decide (Odd (((form m).filter (fun v => assignment x v = true)).card))
def disjointBad (x y : Nat) : Bool := decide (
  (∀ i : Fin 4, (∀ h : Fin 3, assignment x (i,h) = false) →
     ∃ h : Fin 3, assignment y (i,h) = true) ∧
  (∀ i j : Fin 4, ∀ h : Fin 3, i ≠ j → assignment x (i,h) = true → assignment x (j,h) = true →
    assignment y (i,h) = false ∨ assignment y (j,h) = false))
theorem singleton_sat (a : Grid → Bool) (v : Grid) (s : Bool) :
    LinEqSat a ({v},s) ↔ a v = s := by
  unfold LinEqSat
  cases h : a v <;> cases s <;> simp [Finset.filter_singleton,h]
theorem sat_of_disjoint {x y : Nat} (dis : disjointBad x y = true) :
    ∀ D ∈ F, ¬LinClauseSat (assignment x) D → LinClauseSat (assignment y) D := by
  intro D ⟨C,hC,eq⟩; subst D
  have cs := of_decide_eq_true dis
  have lit {a : Grid → Bool} {v : Grid} {s : Bool} (hm : (v,s) ∈ C) (hv : a v = s) :
      LinClauseSat a (linOfClause C) :=
    ⟨({v},s),Finset.mem_image.mpr ⟨(v,s),hm,rfl⟩,(singleton_sat _ _ _).2 hv⟩
  intro reject
  rcases hC with ⟨i,eq⟩ | ⟨i,j,h,ne,eq⟩
  · subst C
    have off (h : Fin 3) : assignment x (i,h) = false := by
      cases e : assignment x (i,h)
      · rfl
      · exact (reject (lit (Finset.mem_image.mpr ⟨h, Finset.mem_univ _,rfl⟩) e)).elim
    obtain ⟨h,on⟩ := cs.1 i off
    exact lit (Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩) on
  · subst C
    have pi : assignment x (i,h) = true := by
      cases e : assignment x (i,h)
      · exact (reject (lit (by simp) e)).elim
      · rfl
    have pj : assignment x (j,h) = true := by
      cases e : assignment x (j,h)
      · exact (reject (lit (by simp) e)).elim
      · rfl
    rcases cs.2 i j h ne pi pj with e | e
    · exact lit (by simp) e
    · exact lit (by simp) e

def checkPack (m : Nat) (b : Bool) (xs : List Nat) : Bool :=
  xs.all (fun x => parity m x == b) &&
  decide (∀ i j : Fin xs.length, i ≠ j → disjointBad xs[i] xs[j] = true)

open PEqualNP.Outside.L_pcx_118.Graph
theorem half_count {C : ClauseMap Grid} {P : Parents} {r m : Nat} {b : Bool} {xs : List Nat}
    (rules : ∀ i ≤ r, Rule F C P i)
    (side : ∀ a : Grid → Bool, decide (Odd (((form m).filter (fun x => a x = true)).card)) = b → FalseAt C a r)
    (check : checkPack m b xs = true) : xs.length ≤ (WithArity P r 0).card := by
  have ⟨all,dis⟩ := Bool.and_eq_true_iff.mp check
  apply packed_leaves rules (fun (t : Fin xs.length) => assignment xs[t])
  · intro t
    apply side
    exact beq_iff_eq.mp (List.all_eq_true.mp all xs[t] (List.getElem_mem ..))
  · intro i j ne
    exact sat_of_disjoint ((of_decide_eq_true dis) i j ne)
end PHPOverlap

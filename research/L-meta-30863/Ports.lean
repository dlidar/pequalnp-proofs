import Boundary
open PEqualNP.CircuitLowerBounds
namespace PortSupport
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def agree (s : Finset Nat) (x y : List Bool) := ∀ i∈s,x.getD i false=y.getD i false

theorem rewind (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length ≤ 2) (m : Nat) (s : Finset Nat) :
    ∃ t : Finset Nat,t.card ≤ s.card+gs.length ∧ ∀ x y : List Bool,x.length=m → y.length=m →
      agree t x y → agree s (gs.foldl step x) (gs.foldl step y) := by
  classical
  induction gs generalizing m with
  | nil => exact ⟨s,by simp,fun _ _ _ _ h => h⟩
  | cons g rest ih =>
    obtain ⟨u,cu,ok⟩ := ih (fun g hg => fan g (by simp [hg])) (m+1)
    let t := if m∈u then u.erase m ∪ g.inputs.toFinset else u
    have len := fan g (by simp)
    have cin := List.toFinset_card_le g.inputs
    refine ⟨t,?_,?_⟩
    · by_cases hu : m∈u
      · have ca := Finset.card_union_le (u.erase m) g.inputs.toFinset
        rw [Finset.card_erase_of_mem hu] at ca
        have cp := Finset.card_pos.mpr ⟨m,hu⟩
        simp only [t,if_pos hu,List.length_cons];omega
      · simp only [t,if_neg hu,List.length_cons];omega
    · intro x y hx hy eq
      apply ok (step x g) (step y g) (by simp [step,hx]) (by simp [step,hy])
      intro i hi
      by_cases same : i=m
      · subst i
        have maps : (g.inputs.map fun j => x.getD j false)=(g.inputs.map fun j => y.getD j false) := by
          apply List.map_congr_left; intro j hj;exact eq j (by simp [t,hi,hj])
        have atEnd (xs : List Bool) (v : Bool) (e : xs.length=m) : (xs++[v]).getD m false=v := by
          rw [← e]; simp [List.getD_eq_getElem?_getD,List.getElem?_append]
        change (x++[_]).getD m false=(y++[_]).getD m false
        rw [atEnd _ _ hx,atEnd _ _ hy,maps]
      · have iint : i∈t := by by_cases hm : m∈u <;> simp [t,hm,hi,same]
        have e := eq i iint
        by_cases ilt : i < m
        · simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,hx,hy,ilt] using (show x.getD i false=y.getD i false from e)
        · have beyond : m+1 ≤ i := by omega
          have lx : (step x g).length ≤ i := by simpa [step,hx] using beyond
          have ly : (step y g).length ≤ i := by simpa [step,hy] using beyond
          simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lx,List.getElem?_eq_none ly]
end PortSupport

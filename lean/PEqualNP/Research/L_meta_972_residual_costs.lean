import PEqualNP.Research.L_meta_4675_star_networks
import PEqualNP.Defs

/-! The two cofactor thresholds in R_meta_972_619 are sharp for shared OR
preprocessing followed by rectangles and a final OR. Deleting either endpoint
of a flag leaves 48 edges. Deleting both leaves 45. In all three cases the
other twelve edges of a cyclic perfect matching survive. -/
namespace PEqualNP.Research.PlaneResidualCosts
open Finset StarNetworks

abbrev V := Fin 13
def flag (a b : V) : Bool := ([(0:ℕ),1,3,9]).contains ((a.val + b.val) % 13)
def surviving (a b : V) (p l : Bool) (i j : V) :=
  flag i j && !(p && decide (i=a)) && !(l && decide (j=b))

def edges (a b : V) (p l : Bool) : Finset (V × V) :=
  univ.filter fun e => surviving a b p l e.1 e.2

def row (a : V) (t : Fin 12) : V := ⟨(a.val+t.val+1)%13, Nat.mod_lt _ (by decide)⟩
def col (a b : V) (t : Fin 12) : V :=
  ⟨(a.val+b.val+13-(row a t).val)%13, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem row_inj : ∀ a, Function.Injective (row a) := by decide +kernel
theorem col_inj : ∀ a b, Function.Injective (col a b) := by decide +kernel

theorem matching : ∀ a b, flag a b → ∀ p l t, (row a t,col a b t) ∈ edges a b p l := by
  decide +kernel

theorem residual_size : ∀ a b, flag a b → ∀ p l, p || l →
    (edges a b p l).card = (if p && l then 45 else 48) := by decide +kernel

theorem flag_thin : ∀ a a' : V, a ≠ a' →
    (univ.filter fun b => flag a b && flag a' b).card ≤ 1 := by decide +kernel

theorem cover_lower (a b : V) (ab : flag a b) (p l : Bool) (S : Finset (Fin 26))
    (cov : ∀ i j, (i,j) ∈ edges a b p l → Fin.castAdd 13 i ∈ S ∨ Fin.natAdd 13 j ∈ S) :
    12 ≤ S.card := by
  let f (t : Fin 12) := if Fin.castAdd 13 (row a t) ∈ S then Fin.castAdd 13 (row a t)
    else Fin.natAdd 13 (col a b t)
  have inside : univ.image f ⊆ S := by
    intro x hx
    obtain ⟨t,_,rfl⟩ := mem_image.mp hx
    dsimp [f]; split
    · assumption
    · exact (cov _ _ (matching a b ab p l t)).resolve_left (by assumption)
  have inj : Function.Injective f := by
    intro i j eq
    have e := congrArg Fin.val eq
    have ri := (row a i).isLt
    have rj := (row a j).isLt
    by_cases hi : Fin.castAdd 13 (row a i) ∈ S <;> by_cases hj : Fin.castAdd 13 (row a j) ∈ S <;>
      simp only [f,hi,hj,ite_true,ite_false,Fin.val_castAdd,Fin.val_natAdd] at e
    · exact row_inj a (Fin.ext e)
    · omega
    · omega
    · exact col_inj a b (Fin.ext (by omega))
  simpa [card_image_of_injective _ inj] using card_le_card inside

theorem thin (a b : V) (p l : Bool) (u u' v v' : V) (hu : u ≠ u') (hv : v ≠ v') :
    ¬ ((u,v) ∈ edges a b p l ∧ (u,v') ∈ edges a b p l ∧
       (u',v) ∈ edges a b p l ∧ (u',v') ∈ edges a b p l) := by
  intro h
  have keep {i j : V} (e : (i,j) ∈ edges a b p l) : flag i j := by
    simp only [edges,surviving,mem_filter,Bool.and_eq_true] at e
    exact e.2.1.1
  apply hv
  apply card_le_one.mp (flag_thin u u' hu)
  · exact mem_filter.mpr ⟨mem_univ _,by simp [keep h.1,keep h.2.2.1]⟩
  · exact mem_filter.mpr ⟨mem_univ _,by simp [keep h.2.1,keep h.2.2.2]⟩

theorem rectangle_cost (a b : V) (ab : flag a b) (p l : Bool) (deleted : p || l)
    (s m : ℕ) (W : ℕ → Finset (Vertex 13 13)) (raw : ∀ i < 26, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ x y, x < 26+j ∧ y < 26+j ∧ W (26+j) = W x ∪ W y)
    (x y : Fin m → ℕ) (valid : ∀ j, x j < 26+s ∧ y j < 26+s)
    (used : ∀ j, (W (x j)).Nonempty ∧ (W (y j)).Nonempty)
    (sound : ∀ j u, u ∈ W (x j) → ∀ v ∈ W (y j), adjacent (edges a b p l) u v)
    (complete : ∀ e ∈ edges a b p l, ∃ j u v, u ∈ W (x j) ∧ v ∈ W (y j) ∧ decode (u,v) = some e) :
    (if p && l then 56 else 59) ≤ s + m + (m-1) := by
  obtain ⟨S,cov,bound⟩ := rectangle_network_bound 13 13 26 s m (edges a b p l)
    (thin a b p l) W raw gate x y valid used sound complete
  have := cover_lower a b ab p l S cov
  rw [residual_size a b ab p l deleted] at bound
  cases p <;> cases l <;> simp at bound ⊢ <;> omega

-- Center the stars on the side where a vertex was removed. Each active
-- center ORs its surviving neighbors, then takes one AND with its own bit.
def leaves (a b : V) (p l : Bool) (i : V) : Finset V :=
  univ.filter fun j => if p then surviving a b p l i j else surviving a b p l j i

def centers (a b : V) (p l : Bool) : Finset V :=
  univ.filter fun i => (leaves a b p l i).Nonempty

def starCost (a b : V) (p l : Bool) : ℕ :=
  let active := centers a b p l
  (∑ i ∈ active, ((leaves a b p l i).card - 1)) + active.card + (active.card - 1)

theorem twelve_centers : ∀ a b, flag a b → ∀ p l, p || l →
    (centers a b p l).card = 12 := by decide +kernel

theorem exact_star_cost : ∀ a b, flag a b → ∀ p l, p || l →
    starCost a b p l = (if p && l then 56 else 59) := by decide +kernel

theorem stars_compute (a b : V) (p l : Bool) (x y : V → Bool) :
    (∃ i ∈ centers a b p l, (if p then x i else y i) = true ∧
      ∃ j ∈ leaves a b p l i, (if p then y j else x j) = true) ↔
    ∃ i j, (i,j) ∈ edges a b p l ∧ x i = true ∧ y j = true := by
  have expand (i : V) : i ∈ centers a b p l ↔ (leaves a b p l i).Nonempty := by
    simp [centers]
  simp only [expand]
  constructor
  · rintro ⟨i,_,hi,j,hj,hv⟩
    cases p
    · exact ⟨j,i,by simpa [leaves,edges] using hj,hv,hi⟩
    · exact ⟨i,j,by simpa [leaves,edges] using hj,hi,hv⟩
  · rintro ⟨i,j,e,hi,hj⟩
    cases p
    · have h : i ∈ leaves a b false l j := by simpa [leaves,edges] using e
      exact ⟨j,⟨i,h⟩,hj,i,h,hi⟩
    · have h : j ∈ leaves a b true l i := by simpa [leaves,edges] using e
      exact ⟨i,⟨j,h⟩,hi,j,h,hj⟩

end PEqualNP.Research.PlaneResidualCosts

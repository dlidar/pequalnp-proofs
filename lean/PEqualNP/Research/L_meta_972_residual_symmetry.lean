import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.Defs

namespace PEqualNP.Research.PlaneResidualSymmetry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev V := Fin 26
def near (u v : V) : Prop := u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ)
instance (u v : V) : Decidable (near u v) := by unfold near; infer_instance

def edge (u v : V) := near u v ∨ near v u
instance (u v : V) : Decidable (edge u v) := by unfold edge; infer_instance

def hit (S : Finset V) (x : V → Bool) :=
  ∃ u v, edge u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true

def bound (S : Finset V) (k : ℕ) :=
  ∀ C : Circuit, Monotone2 C → (∀ x, C.eval (List.ofFn x) = true ↔ hit S x) → k ≤ C.size

theorem transport (S T : Finset V) (π : V → V) (onto : Function.Surjective π)
    (graph : ∀ u v, edge (π u) (π v) ↔ edge u v)
    (mask : ∀ i, π i ∈ T ↔ i ∈ S) (k : ℕ) (hb : bound T k) : bound S k := by
  intro C hm he
  let D := relabel 26 26 π C
  have dm : Monotone2 D := by
    intro g hg
    change g ∈ C.gates.map (relGate 26 26 π) at hg
    obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm g0 h0).1,by simpa [relGate] using (hm g0 h0).2⟩
  have de (x : V → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
    (rel_fold 26 26 π C.gates _ _ (rel_init 26 26 π x)).2.2 C.output
  have lb := hb D dm (by
    intro x
    rw [de,he]
    constructor
    · rintro ⟨u,v,e,hu,hv,xu,xv⟩
      exact ⟨π u,π v,(graph u v).mpr e,fun h => hu ((mask u).mp h),fun h => hv ((mask v).mp h),xu,xv⟩
    · rintro ⟨u,v,e,hu,hv,xu,xv⟩
      obtain ⟨i,rfl⟩ := onto u
      obtain ⟨j,rfl⟩ := onto v
      exact ⟨i,j,(graph i j).mp e,fun h => hu ((mask i).mpr h),fun h => hv ((mask j).mpr h),xu,xv⟩)
  simpa [D,relabel,Circuit.size] using lb

-- A translation sends the point to zero. Four explicit collineations of
-- the cyclic plane then send its marked line to zero as well.
def shift (a i : V) : V := if i.val < 13 then Fin.ofNat 26 ((i.val+13-a.val)%13)
  else Fin.ofNat 26 (13+(i.val+a.val)%13)
def dual (i : V) : V := Fin.ofNat 26 ((i.val+13)%26)
def map0 (i : V) : V := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] : Array V)[i.val]!
def map1 (i : V) : V := (#[0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9, 14, 13, 20, 16, 17, 23, 19, 15, 24, 22, 18, 21, 25] : Array V)[i.val]!
def map3 (i : V) : V := (#[0, 2, 11, 8, 5, 4, 1, 7, 10, 12, 3, 9, 6, 14, 16, 20, 13, 23, 17, 19, 15, 25, 22, 21, 18, 24] : Array V)[i.val]!
def map9 (i : V) : V := (#[0, 2, 10, 8, 1, 3, 5, 9, 11, 12, 4, 7, 6, 14, 16, 20, 22, 23, 15, 18, 17, 24, 13, 21, 19, 25] : Array V)[i.val]!

def collineation (d : ℕ) : V → V :=
  if d=1 then map1 else if d=3 then map3 else if d=9 then map9 else map0
def pairMap (a b i : V) : V := collineation ((a.val+b.val)%13) (shift a i)
def singleMap (a i : V) : V := if a.val < 13 then shift a i else shift (dual a) (dual i)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem single_onto : ∀ a, Function.Surjective (singleMap a) := by decide +kernel
theorem single_edges : ∀ a u v, edge (singleMap a u) (singleMap a v) ↔ edge u v := by decide +kernel
theorem single_mask : ∀ a i, singleMap a i = 0 ↔ i = a := by decide +kernel

theorem col_edges : ∀ d : Fin 13, ∀ u v, edge (collineation d.val u) (collineation d.val v) ↔ edge u v := by decide +kernel
theorem shift_edges : ∀ a : Fin 13, ∀ u v, edge (shift (Fin.castAdd 13 a) u) (shift (Fin.castAdd 13 a) v) ↔ edge u v := by decide +kernel
theorem pair_edges (a b : V) (h : near a b) (u v : V) :
    edge (pairMap a b u) (pairMap a b v) ↔ edge u v := by
  let d : Fin 13 := ⟨(a.val+b.val)%13,Nat.mod_lt _ (by decide)⟩
  let i : Fin 13 := ⟨a.val,h.1⟩
  exact (col_edges d _ _).trans (shift_edges i u v)

theorem pair_onto : ∀ a b, near a b → Function.Surjective (pairMap a b) := by decide +kernel
theorem pair_mask : ∀ a b, near a b → ∀ i, (pairMap a b i = 0 ∨ pairMap a b i = 13) ↔ i = a ∨ i = b := by decide +kernel

theorem one_representative (k : ℕ) : (∀ a : V, bound {a} k) ↔ bound {0} k := by
  refine ⟨fun h => h 0,?_⟩
  intro h a
  exact transport _ _ _ (single_onto a) (single_edges a) (by simpa using single_mask a) k h

theorem flag_representative (k : ℕ) : (∀ a b : V, near a b → bound {a,b} k) ↔ bound {0,13} k := by
  refine ⟨fun h => h 0 13 (by decide),?_⟩
  intro h a b ab
  exact transport _ _ _ (pair_onto a b ab) (pair_edges a b ab) (by simpa using pair_mask a b ab) k h

theorem oriented (S : Finset V) (x : V → Bool) : hit S x ↔
    ∃ u v, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u,v,h,hu,hv,xu,xv⟩
    rcases h with h|h
    · exact ⟨u,v,h,hu,hv,xu,xv⟩
    · exact ⟨v,u,h,hv,hu,xv,xu⟩
  · rintro ⟨u,v,h,hu,hv,xu,xv⟩
    exact ⟨u,v,Or.inl h,hu,hv,xu,xv⟩

/-- The second child of the fork reduction follows from one 59-gate inequality. -/
theorem single_child (h : bound {0} 59) :
    ∀ k : Fin 26, let S : Finset (Fin 26) := {k}
      ∀ R : Circuit, Monotone2 R → (∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
        ∃ u v, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true) → 59 ≤ R.size := by
  intro k
  dsimp only
  intro R hm ok
  exact (one_representative 59).mpr h k R hm (fun x => (ok x).trans (oriented {k} x).symm)

/-- The third child follows from one 56-gate inequality. -/
theorem pair_child (h : bound {0,13} 56) :
    ∀ i j : Fin 26, near i j → let S : Finset (Fin 26) := {i,j}
      ∀ R : Circuit, Monotone2 R → (∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
        ∃ u v, near u v ∧ u ∉ S ∧ v ∉ S ∧ x u = true ∧ x v = true) → 56 ≤ R.size := by
  intro i j hij
  dsimp only
  intro R hm ok
  exact (flag_representative 56).mpr h i j hij R hm (fun x => (ok x).trans (oriented {i,j} x).symm)

end PEqualNP.Research.PlaneResidualSymmetry

import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Research.L_meta_4675_star_networks

namespace PEqualNP.Research.FiveRows
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.StarNetworks Finset

def readRow (data : List ℕ) (r : ℕ) (i : Fin 20) : Bool :=
  (data.getD (r/3) 0).testBit (20*(r%3)+i.val)
def pos (r : Fin 20) := readRow [882706627014164513, 72567803150337, 74801153180674, 72062818869837956, 720866211591618600, 720875007625924616, 8606712336] r.val
def neg (r : Fin 44) := readRow [4665232155738143, 13518504604999695, 725368754528096277, 730724029253162005, 866973350870287389, 875963053248350355, 884986756446568478, 903000063497490454, 954792603833647132, 1012212425860929682, 1041183516279060867, 1062218301194542225, 1078371242023506996, 1142983005070916482, 1099479117384] r.val
def passes (C : Circuit) : Prop :=
  (∀ r, circuitFun 20 C (pos r) = true) ∧ (∀ r, circuitFun 20 C (neg r) = false)

def refCircuit : Circuit := ⟨[⟨.or,[5,9]⟩,
  ⟨.or,[14,16]⟩,
  ⟨.or,[20,21]⟩,
  ⟨.and,[0,22]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[10,15]⟩,
  ⟨.or,[24,25]⟩,
  ⟨.and,[1,26]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.or,[11,16]⟩,
  ⟨.or,[28,29]⟩,
  ⟨.and,[2,30]⟩,
  ⟨.or,[5,7]⟩,
  ⟨.or,[8,12]⟩,
  ⟨.or,[32,33]⟩,
  ⟨.and,[3,34]⟩,
  ⟨.or,[6,8]⟩,
  ⟨.or,[9,13]⟩,
  ⟨.or,[36,37]⟩,
  ⟨.and,[4,38]⟩,
  ⟨.or,[39,35]⟩,
  ⟨.or,[40,31]⟩,
  ⟨.or,[41,27]⟩,
  ⟨.or,[42,23]⟩],43⟩

theorem reference_size : refCircuit.size = 24 := rfl
theorem reference_mono : Monotone2 refCircuit := by
  intro g hg
  simp only [refCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem reference_passes : passes refCircuit := by
  constructor <;> decide +kernel

def colMask (a : Fin 5) := ([2577, 1059, 2118, 141, 282] : List ℕ).getD a.val 0
def E : Finset (Fin 5 × Fin 15) := univ.filter fun e => (colMask e.1).testBit e.2.val
def idx : Vertex 5 15 → Fin 20
  | .inl a => Fin.castAdd 15 a
  | .inr b => Fin.natAdd 5 b
instance (u v : Vertex 5 15) : Decidable (adjacent E u v) := by
  cases u <;> cases v <;> unfold adjacent <;> infer_instance

theorem graph_size : E.card = 20 := by decide +kernel
theorem graph_thin : fourFree E := by unfold fourFree; decide +kernel
theorem negative_cert : ∀ u v : Vertex 5 15, ¬ adjacent E u v →
    ∃ k, neg k (idx u) = true ∧ neg k (idx v) = true := by decide +kernel

def positives_only_edge (k : Fin 20) (e : Fin 5 × Fin 15) : Prop :=
  ∀ u v : Vertex 5 15, pos k (idx u) = true → pos k (idx v) = true →
    adjacent E u v → decode (u,v) = some e
instance (k e) : Decidable (positives_only_edge k e) := by unfold positives_only_edge; infer_instance

theorem positive_cert : ∀ e ∈ E, ∃ k, positives_only_edge k e := by decide +kernel

def mate (i : Fin 5) : Fin 15 := ([9,10,6,7,8] : List (Fin 15)).getD i.val 0
theorem mates : (∀ i, (i,mate i) ∈ E) ∧ (∀ i j, mate i = mate j → i = j) := by decide +kernel

theorem cover_five (S : Finset (Fin 20)) (h : ∀ a b, (a,b) ∈ E →
    Fin.castAdd 15 a ∈ S ∨ Fin.natAdd 5 b ∈ S) : 5 ≤ S.card := by
  let f (i : Fin 5) : Fin 20 := if Fin.castAdd 15 i ∈ S then Fin.castAdd 15 i else Fin.natAdd 5 (mate i)
  have inc : univ.image f ⊆ S := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    dsimp [f]
    split
    · assumption
    · exact (h _ _ (mates.1 i)).resolve_left (by assumption)
  have inj : Function.Injective f := by
    intro i j eq
    have e := congrArg Fin.val eq
    by_cases hi : Fin.castAdd 15 i ∈ S <;> by_cases hj : Fin.castAdd 15 j ∈ S <;>
      simp only [f,hi,hj,ite_true,ite_false, Fin.val_castAdd,Fin.val_natAdd] at e
    · exact Fin.ext e
    · have := i.isLt; omega
    · have := j.isLt; omega
    · apply mates.2 i j; apply Fin.ext; omega
  simpa [card_image_of_injective _ inj] using card_le_card inc

/-- Any OR preprocessing network feeding nonempty two-sided products, combined by OR,
needs at least 24 gates on the posted tests. OR wires may be shared across products. -/
theorem shared_network_lower (n s m : ℕ) (W : ℕ → Finset (Vertex 5 15))
    (raw : ∀ i < n, (W i).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧ W (n+j) = W a ∪ W b)
    (x y : Fin m → ℕ) (valid : ∀ j, x j < n+s ∧ y j < n+s)
    (used : ∀ j, (W (x j)).Nonempty ∧ (W (y j)).Nonempty)
    (yes : ∀ k, ∃ j u v, u ∈ W (x j) ∧ v ∈ W (y j) ∧
      pos k (idx u) = true ∧ pos k (idx v) = true)
    (no : ∀ k j u v, u ∈ W (x j) → v ∈ W (y j) →
      neg k (idx u) = true → neg k (idx v) = false) :
    24 ≤ s + m + (m-1) := by
  have sound : ∀ j u, u ∈ W (x j) → ∀ v ∈ W (y j), adjacent E u v := by
    intro j u hu v hv
    by_contra h
    obtain ⟨k,h1,h2⟩ := negative_cert u v h
    rw [no k j u v hu hv h1] at h2
    contradiction
  obtain ⟨S,cover,bound⟩ := rectangle_network_bound 5 15 n s m E graph_thin W raw gate x y valid used sound (by
    intro e he
    obtain ⟨k,hk⟩ := positive_cert e he
    obtain ⟨j,u,v,hu,hv,pu,pv⟩ := yes k
    exact ⟨j,u,v,hu,hv,hk u v pu pv (sound j u hu v hv)⟩)
  have := cover_five S cover
  rw [graph_size] at bound
  omega


/-- All seventeen non-marker input coordinates are essential even if all marker
variables can be used in an unrestricted monotone circuit. -/
theorem essential_tests : ∀ i : Fin 17, ∃ r k, ∀ j : Fin 20,
    j.val ≠ i.val → pos r j = true → neg k j = true := by decide +kernel

theorem support_lower (C : Circuit) (hm : Monotone2 C) (ok : passes C) : 16 ≤ C.size := by
  obtain ⟨T,sz,det⟩ := circuit_support 20 C (fun g hg => (hm g hg).2)
  have subset : range 17 ⊆ T := by
    intro i hi
    by_contra absent
    obtain ⟨r,k,sep⟩ := essential_tests ⟨i,mem_range.mp hi⟩
    let z := fun j : Fin 20 => pos r j && neg k j
    have eq := det (pos r) z (by
      intro j hj
      have hne : j.val ≠ i := fun he => absent (he ▸ hj)
      cases h : pos r j
      · simp [z,h]
      · simp [z,h,sep j hne h])
    have mono : circuitFun 20 C z = true → circuitFun 20 C (neg k) = true := by
      apply LowMergeProof.wires_mono C (fun g hg => (hm g hg).1) _ _ (by simp) _ C.output
      intro j
      by_cases hj : j < 20
      · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simpa using hj)]
        simp only [List.getElem_ofFn,z,Bool.and_eq_true]
        exact And.right
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
        exact id
    have bad := mono (eq ▸ ok.1 r)
    rw [ok.2 k] at bad
    contradiction
  have := card_le_card subset
  rw [card_range] at this
  omega

-- Project the tests to the 17 primary coordinates. The row side is encoded
-- by five bits and the column side is a set of the twelve ordinary columns.
abbrev Cols := Finset (Fin 12)
def below (a b : Fin 32) : Prop := a.val &&& b.val = a.val
instance (a b) : Decidable (below a b) := inferInstanceAs (Decidable (_ = _))
def rowPart (f : Fin 20 → Bool) : Fin 32 :=
  ⟨((List.range 5).foldl (fun a i => if f (Fin.ofNat 20 i) then a + 2^i else a) 0) % 32, Nat.mod_lt _ (by decide)⟩
def colPart (f : Fin 20 → Bool) : Cols := univ.filter fun j => f (Fin.ofNat 20 (5+j.val))
def up (a : Fin 32) (B : Cols) : Prop := ∃ k, below (rowPart (pos k)) a ∧ colPart (pos k) ⊆ B
def down (a : Fin 32) (B : Cols) : Prop := ∃ k, below a (rowPart (neg k)) ∧ B ⊆ colPart (neg k)
instance (a B) : Decidable (up a B) := by unfold up; infer_instance
instance (a B) : Decidable (down a B) := by unfold down; infer_instance
def avoid (a : Fin 32) : Cols := univ.filter fun j =>
  ∀ i : Fin 5, a.val.testBit i.val = true → (colMask i).testBit j.val = false
def holes : Finset (Fin 32) := {7,13,14,19,21,25,26,28}
theorem holes_card : holes.card = 8 := by decide
theorem adjacent_positive : ∀ (a : Fin 32) (j : Fin 12), j ∉ avoid a →
    ∃ k, below (rowPart (pos k)) a ∧ colPart (pos k) = {j} := by decide +kernel
theorem maximal_tests : ∀ a, (a ∈ holes ↔ ¬ down a (avoid a)) ∧ ¬ up a (avoid a) := by decide +kernel
theorem deletion_tests : ∀ a ∈ holes, ∀ j ∈ avoid a, down a ((avoid a).erase j) := by decide +kernel

/-- On the 2^17 projected inputs the positive and negative closures leave
exactly eight inputs unspecified, one maximal independent input per listed row mask. -/
theorem projected_boundary (a : Fin 32) (B : Cols) :
    (¬ up a B ∧ ¬ down a B) ↔ a ∈ holes ∧ B = avoid a := by
  constructor
  · rintro ⟨hp,hn⟩
    have sub : B ⊆ avoid a := by
      intro j hj
      by_contra out
      obtain ⟨k,hk,hj'⟩ := adjacent_positive a j out
      exact hp ⟨k,hk,hj' ▸ singleton_subset_iff.mpr hj⟩
    have maximal : ¬ down a (avoid a) := by
      rintro ⟨k,hk,hc⟩
      exact hn ⟨k,hk,sub.trans hc⟩
    have hole := (maximal_tests a).1.mpr maximal
    refine ⟨hole,Subset.antisymm sub ?_⟩
    intro j hj
    by_contra absent
    obtain ⟨k,hk,hc⟩ := deletion_tests a hole j hj
    apply hn
    exact ⟨k,hk,(subset_erase.mpr ⟨sub,absent⟩).trans hc⟩
  · rintro ⟨h,rfl⟩
    exact ⟨(maximal_tests a).2,(maximal_tests a).1.mp h⟩

def tableMono (F : Fin 32 → Cols → Prop) : Prop :=
  ∀ a b U V, below a b → U ⊆ V → F a U → F b V
def tableFits (F : Fin 32 → Cols → Prop) : Prop :=
  (∀ r, F (rowPart (pos r)) (colPart (pos r))) ∧
  ∀ k, ¬ F (rowPart (neg k)) (colPart (neg k))

def completion (chosen : Finset (Fin 32)) (a : Fin 32) (X : Cols) : Prop :=
  up a X ∨ (a ∈ chosen ∧ X = avoid a)

private theorem bit_refl : ∀ a : Fin 32, below a a := by decide +kernel
private theorem bit_trans (a b c : Fin 32) (h : below a b) (g : below b c) : below a c := by
  change a.val &&& b.val = a.val at h
  change b.val &&& c.val = b.val at g
  change a.val &&& c.val = a.val
  calc
    _ = (a.val &&& b.val) &&& c.val := congrArg (· &&& c.val) h.symm
    _ = a.val := by rw [Nat.and_assoc,g,h]

private theorem up_mono : tableMono up := by
  rintro a b U V ab uv ⟨k,kr,kc⟩
  exact ⟨k,bit_trans _ _ _ kr ab,kc.trans uv⟩

theorem row_extension : ∀ a ∈ holes, ∀ b, below a b → a ≠ b → up b (avoid a) := by decide +kernel
theorem negative_consistency : ∀ k, ¬ up (rowPart (neg k)) (colPart (neg k)) := by decide +kernel

/-- Every choice of the eight free entries gives a monotone extension of the
projected tests, and distinct choices give distinct tables. -/
theorem completion_realizes (chosen : Finset (Fin 32)) (sub : chosen ⊆ holes) :
    tableMono (completion chosen) ∧ tableFits (completion chosen) ∧
    ∀ a ∈ holes, completion chosen a (avoid a) ↔ a ∈ chosen := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · rintro a b U V ab uv (hu | ⟨ha,rfl⟩)
    · exact Or.inl (up_mono _ _ _ _ ab uv hu)
    by_cases h : a = b
    · subst b
      by_cases eq : V = avoid a
      · exact Or.inr ⟨ha,eq⟩
      · obtain ⟨j,hj,hout⟩ := IsConcreteLE.not_le_iff_exists.mp (fun hsub : V ⊆ avoid a => eq (Subset.antisymm hsub uv))
        obtain ⟨k,kr,kc⟩ := adjacent_positive a j hout
        exact Or.inl ⟨k,kr,kc ▸ singleton_subset_iff.mpr hj⟩
    · exact Or.inl (up_mono _ _ _ _ (bit_refl b) uv (row_extension a (sub ha) b ab h))
  · intro r
    exact Or.inl ⟨r,bit_refl _,Subset.rfl⟩
  · rintro k (bad | ⟨hk,eq⟩)
    · exact negative_consistency k bad
    · apply (maximal_tests _).1.mp (sub hk)
      exact ⟨k,bit_refl _,eq ▸ Subset.rfl⟩
  · intro a ha
    exact ⟨fun h => h.elim (fun u => False.elim ((maximal_tests a).2 u)) And.left, fun h => Or.inr ⟨h,rfl⟩⟩

theorem projected_classification (F : Fin 32 → Cols → Prop) (mon : tableMono F)
    (fits : tableFits F) : ∃ chosen ⊆ holes, ∀ a X, F a X ↔ completion chosen a X := by
  classical
  refine ⟨holes.filter (fun a => F a (avoid a)),filter_subset _ _,?_⟩
  intro a X
  constructor
  · intro fx
    by_cases u : up a X
    · exact Or.inl u
    have nd : ¬down a X := by
      rintro ⟨k,ka,kx⟩
      exact fits.2 k (mon _ _ _ _ ka kx fx)
    obtain ⟨ha,rfl⟩ := (projected_boundary a X).mp ⟨u,nd⟩
    exact Or.inr ⟨mem_filter.mpr ⟨ha,fx⟩,rfl⟩
  · rintro (⟨k,ka,kx⟩ | ⟨h,rfl⟩)
    · exact mon _ _ _ _ ka kx (fits.1 k)
    · exact (mem_filter.mp h).2

-- Set all three markers true. These conclusions apply even when the circuit
-- uses every marker. Only negative samples with all markers true can bound
-- a point on this slice from above.
def marked (a : Fin 32) (X : Cols) (i : Fin 20) : Bool :=
  if i.val < 5 then a.val.testBit i.val
  else if i.val < 17 then decide (Fin.ofNat 12 (i.val-5) ∈ X) else true
def high (k : Fin 44) := neg k 17 && neg k 18 && neg k 19
def highDown (a : Fin 32) (X : Cols) : Prop :=
  ∃ k, high k = true ∧ below a (rowPart (neg k)) ∧ X ⊆ colPart (neg k)
instance (a X) : Decidable (highDown a X) := by unfold highDown; infer_instance

private theorem marked_mono {a b : Fin 32} {X Y : Cols} (ab : below a b) (xy : X ⊆ Y) :
    ∀ i, marked a X i = true → marked b Y i = true := by
  have bits : ∀ (c d : Fin 32), below c d → ∀ j : Fin 5,
      c.val.testBit j.val = true → d.val.testBit j.val = true := by decide +kernel
  intro i
  by_cases h : i.val < 5
  · simpa [marked,h] using bits a b ab ⟨i.val,h⟩
  · by_cases k : i.val < 17
    · simpa [marked,h,k] using (fun hx => xy hx : Fin.ofNat 12 (i.val-5) ∈ X → _)
    · simp [marked,h,k]

private theorem liftPos : ∀ r i, pos r i = true →
    marked (rowPart (pos r)) (colPart (pos r)) i = true := by decide +kernel
private theorem liftNeg : ∀ k, high k = true → ∀ i,
    marked (rowPart (neg k)) (colPart (neg k)) i = true → neg k i = true := by decide +kernel

private theorem eval_mono (C : Circuit) (hm : Monotone2 C) (f g : Fin 20 → Bool)
    (fg : ∀ i, f i = true → g i = true) :
    circuitFun 20 C f = true → circuitFun 20 C g = true := by
  apply LowMergeProof.wires_mono C (fun t ht => (hm t ht).1) _ _ (by simp) _ C.output
  intro k
  by_cases hk : k < 20
  · rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getD_eq_getElem _ _ (by simpa using hk)]
    simpa only [List.getElem_ofFn] using fg ⟨k,hk⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]; exact id

def unknownCols (a : Fin 32) : Finset Cols :=
  if highDown a (avoid a) then ∅ else (avoid a).powerset.filter fun X => ¬highDown a X

theorem high_slice_count : ∑ a : Fin 32, (unknownCols a).card = 173 := by
  set_option maxRecDepth 32768 in
  set_option maxHeartbeats 4000000 in decide +kernel

theorem high_slice_spec (a : Fin 32) (X : Cols) :
    X ∈ unknownCols a ↔ ¬up a X ∧ ¬highDown a X := by
  have downMono {B Y : Cols} (sub : B ⊆ Y) : highDown a Y → highDown a B := by
    rintro ⟨k,h,r,c⟩; exact ⟨k,h,r,sub.trans c⟩
  have hn : (¬up a X) ↔ X ⊆ avoid a := by
    constructor
    · intro u j hj
      by_contra out
      obtain ⟨k,kr,eq⟩ := adjacent_positive a j out
      exact u ⟨k,kr,eq ▸ singleton_subset_iff.mpr hj⟩
    · intro sub h
      exact (maximal_tests a).2 (up_mono _ _ _ _ (bit_refl a) sub h)
  rw [hn]
  unfold unknownCols
  split
  · rename_i h
    simpa only [notMem_empty, false_iff, not_and] using fun (sub : X ⊆ avoid a) => not_not_intro (downMono sub h)
  · simp

theorem high_slice_forced (C : Circuit) (hm : Monotone2 C) (fits : passes C)
    (a : Fin 32) (X : Cols) (fixed : X ∉ unknownCols a) :
    circuitFun 20 C (marked a X) = true ↔ up a X := by
  constructor
  · intro yes
    by_contra notUp
    have : highDown a X := by
      by_contra nd
      exact fixed ((high_slice_spec a X).mpr ⟨notUp,nd⟩)
    obtain ⟨k,h,kr,kc⟩ := this
    have bad := eval_mono C hm _ _ (fun i hi => liftNeg k h i (marked_mono kr kc i hi)) yes
    rw [fits.2 k] at bad
    contradiction
  · rintro ⟨k,kr,kc⟩
    exact eval_mono C hm _ _ (fun i hi => marked_mono kr kc i (liftPos k i hi)) (fits.1 k)
-- Confirm the test interface against the posted proposition by definitional equality.
theorem statement_eq : (¬ (have x1 : List ℕ → ℕ → Fin (20 : ℕ) → Bool := fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (20 : ℕ)) => (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (x2 % (3 : ℕ)) + ↑x3); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ (∀ (x3 : Fin (20 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(882706627014164513 : ℕ), (72567803150337 : ℕ), (74801153180674 : ℕ), (72062818869837956 : ℕ), (720866211591618600 : ℕ), (720875007625924616 : ℕ), (8606712336 : ℕ)] ↑x3) = Bool.true) ∧ ∀ (x3 : Fin (44 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)] ↑x3) = Bool.false)) ↔
    ¬ ∃ C, Monotone2 C ∧ C.size ≤ 23 ∧ passes C := Iff.rfl

end PEqualNP.Research.FiveRows

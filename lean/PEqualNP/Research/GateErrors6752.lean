import PEqualNP.Research.Rectangle6752

namespace PEqualNP.Research.GateErrors6752

open PEqualNP.Research.Residual6752 PEqualNP.Research.ResidualConnection6752
open PEqualNP.Research.Overlap6752 PEqualNP.Research.Rectangle6752
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_8005

def bad (L R : Finset V) := (touched L ∩ touched R) \ graph.edgeFinset
def unpack (p : V × V) : Edge := s(p.1,p.2)

theorem bad_mono {L R L' R' : Finset V} (hl : L ⊆ L') (hr : R ⊆ R') : bad L R ⊆ bad L' R' := by
  intro e h
  obtain ⟨both,neg⟩ := Finset.mem_sdiff.mp h
  obtain ⟨l,r⟩ := Finset.mem_inter.mp both
  obtain ⟨x,hx,hxe⟩ := (touches L _).mp l
  obtain ⟨y,hy,hye⟩ := (touches R _).mp r
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨(touches L' e).mpr ⟨x,hl hx,hxe⟩,
    (touches R' e).mpr ⟨y,hr hy,hye⟩⟩,neg⟩

theorem disjoint_count (L R : Finset V) (h : Disjoint L R) :
    ((crossNeg L R).image unpack).card = (crossNeg L R).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
  obtain ⟨ar,bl⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  obtain ⟨cr,dl⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hcd).1
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact (Finset.disjoint_left.mp h bl cr).elim

theorem combined (L R : Finset V) :
    (forced graph (L ∩ R)).card + (crossNeg (L \ R) (R \ L)).card ≤ (bad L R).card := by
  let D := (crossNeg (L \ R) (R \ L)).image unpack
  have sub : D ⊆ bad L R := by
    intro e h
    obtain ⟨⟨a,b⟩,hh,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ab,neg⟩ := Finset.mem_filter.mp hh
    obtain ⟨ar,bl⟩ := Finset.mem_product.mp ab
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
      ⟨(touched_iff L a b).2 (.inr (Finset.mem_sdiff.mp bl).1),
       (touched_iff R a b).2 (.inl (Finset.mem_sdiff.mp ar).1)⟩,by simpa [unpack] using neg⟩
  have subF : forced graph (L ∩ R) ⊆ bad L R := by
    intro e h
    obtain ⟨hit,neg⟩ := Finset.mem_sdiff.mp h
    obtain ⟨x,hx,he⟩ := (touches _ e).mp hit
    obtain ⟨lx,rx⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
      ⟨(touches _ _).2 ⟨x,lx,he⟩,(touches _ _).2 ⟨x,rx,he⟩⟩,neg⟩
  have dj : Disjoint (forced graph (L ∩ R)) D := by
    apply Finset.disjoint_left.mpr
    intro e hF hD
    obtain ⟨⟨a,b⟩,hh,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨ar,bl⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hh).1
    rcases (touched_iff (L ∩ R) a b).mp (Finset.mem_sdiff.mp hF).1 with left | right
    · exact (Finset.mem_sdiff.mp ar).2 (Finset.mem_inter.mp left).1
    · exact (Finset.mem_sdiff.mp bl).2 (Finset.mem_inter.mp right).2
  have sep : Disjoint (L \ R) (R \ L) := Finset.disjoint_left.mpr (fun _ hl hr =>
    (Finset.mem_sdiff.mp hl).2 (Finset.mem_sdiff.mp hr).1)
  have c := Finset.card_le_card (Finset.union_subset subF sub)
  rw [Finset.card_union_of_disjoint dj, show D.card = _ from disjoint_count _ _ sep] at c
  exact c

def lower (k : Nat) := k * k - maximum k

theorem equal_sides (L R : Finset V) (sz : R.card = L.card) (sm : L.card ≤ 5) :
    lower L.card ≤ (bad L R).card := by
  let k := L.card
  let t := (L ∩ R).card
  have tsmall : t ≤ k := Finset.card_le_card Finset.inter_subset_left
  have ls : (L \ R).card = k-t := by rw [Finset.card_sdiff,Finset.inter_comm]
  have rs : (R \ L).card = k-t := by rw [Finset.card_sdiff,sz]
  have dj : Disjoint (L \ R) (R \ L) := Finset.disjoint_left.mpr (fun _ hl hr =>
    (Finset.mem_sdiff.mp hl).2 (Finset.mem_sdiff.mp hr).1)
  have a := false_pairs (L \ R) (R \ L) dj (rs.trans ls.symm) (by dsimp [k] at ls; omega)
  rw [ls] at a
  have b := overlap_lower (L ∩ R)
  have c := combined L R
  have tab : ∀ i j : Fin 6, j.val ≤ i.val →
      lower i.val ≤ minimum j.val + ((i.val-j.val)*(i.val-j.val) - maximum (i.val-j.val)) := by decide +kernel
  have key := tab ⟨k,by dsimp [k]; omega⟩ ⟨t,by dsimp [k] at tsmall; omega⟩ tsmall
  exact key.trans ((Nat.add_le_add b a).trans c)

theorem any_sides (L R : Finset V) (k : Nat) (kl : k ≤ L.card) (kr : k ≤ R.card) (sm : k ≤ 5) :
    lower k ≤ (bad L R).card := by
  obtain ⟨l,hl,lc⟩ := Finset.exists_subset_card_eq kl
  obtain ⟨r,hr,rc⟩ := Finset.exists_subset_card_eq kr
  have b := equal_sides l r (rc.trans lc.symm) (lc ▸ sm)
  rw [lc] at b
  exact b.trans (Finset.card_le_card (bad_mono hl hr))

def witnesses : Fin 6 → Finset V × Finset V
  | 0 => (∅,∅)
  | 1 => ({0},{9})
  | 2 => ({0,2},{5,10})
  | 3 => ({0,4,5},{8,9,10})
  | 4 => ({0,2,4,8},{1,5,9,10})
  | _ => ({0,4,5,6,7},{1,3,8,9,10})

theorem exact : ∀ k : Fin 6, (witnesses k).1.card = k.val ∧ (witnesses k).2.card = k.val ∧
    (bad (witnesses k).1 (witnesses k).2).card = lower k ∧
    lower k = [0,0,1,3,7,14][k.val]! := by decide +kernel

theorem gate_bound (C : Circuit) (ao : IsAO2 11 C) {g : Nat} (hg : g ∈ junk graph C)
    (k : Nat) (kl : ∀ b : Fin 2, k ≤ (side (n := 11) C g b).card) (sm : k ≤ 5) :
    ∃ errors : Finset Edge, lower k ≤ errors.card ∧ ∀ u v : V, s(u,v) ∈ errors →
      PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ (pairInput u v) = false ∧
      gateVal 11 C g (pairInput u v) = true := by
  let L := side (n := 11) C g 0
  let R := side (n := 11) C g 1
  refine ⟨bad L R,any_sides L R k (kl 0) (kl 1) sm,?_⟩
  intro u v h
  obtain ⟨both,neg⟩ := Finset.mem_sdiff.mp h
  obtain ⟨left,right⟩ := Finset.mem_inter.mp both
  obtain ⟨len,op,_⟩ := junkData hg
  constructor
  · apply Bool.eq_false_iff.mpr
    exact fun yes => neg (by simpa using (graphFun_pair graph u v).mp yes)
  · rcases (touched_iff L u v).mp left with hl | hl <;>
      rcases (touched_iff R u v).mp right with hr | hr
    · exact andFromInputs ao len op hl hr (pairInput_left u v) (pairInput_left u v)
    · exact andFromInputs ao len op hl hr (pairInput_left u v) (pairInput_right u v)
    · exact andFromInputs ao len op hl hr (pairInput_right u v) (pairInput_left u v)
    · exact andFromInputs ao len op hl hr (pairInput_right u v) (pairInput_right u v)


def pairMask (e : Edge) : V → Bool := fun w => decide (w ∈ e)

theorem pairMask_mk (u v : V) : pairMask s(u,v) = pairInput u v := by
  funext w
  simp [pairMask,pairInput,Sym2.mem_iff]

def firstAt (C : Circuit) (g : Nat) (e : Edge) : Prop :=
  g ∈ junk graph C ∧ gateVal 11 C g (pairMask e) = true ∧
    ∀ j ∈ junk graph C, j < g → gateVal 11 C j (pairMask e) = false

theorem unique_first (C : Circuit) (e : Edge) {g j : Nat} (h : firstAt C g e)
    (h' : firstAt C j e) : g = j := by
  rcases lt_trichotomy g j with lt | eq | gt
  · exact (Bool.false_ne_true ((h'.2.2 g h.1 lt).symm.trans h.2.1)).elim
  · exact eq
  · exact (Bool.false_ne_true ((h.2.2 j h'.1 gt).symm.trans h'.2.1)).elim

theorem first_hits (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    (e : Edge) (he : e ∈ Ustar graph C) :
    ∃ g, firstAt C g e ∧ ∀ b : Fin 2, ∃ v ∈ e, v ∈ side C g b := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨g,hg,hit,prior,sides⟩ := firstResidualGate least top he
    refine ⟨g,?_,?_⟩
    · simpa only [firstAt,pairMask_mk] using And.intro hg (And.intro hit prior)
    · intro b
      rcases sides b with h | h
      · exact ⟨u,Sym2.mem_mk_left _ _,h⟩
      · exact ⟨v,Sym2.mem_mk_right _ _,h⟩

theorem matching_hits (M : Finset Edge) (S : Finset V)
    (matching : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset)
    (hits : ∀ e ∈ M, ∃ v ∈ e, v ∈ S) : M.card ≤ S.card := by
  classical
  let rep (e : Edge) : V := if h : e ∈ M then Classical.choose (hits e h) else 0
  have spec (e : Edge) (h : e ∈ M) : rep e ∈ e ∧ rep e ∈ S := by
    simp only [rep,dite_eq_left h]
    exact Classical.choose_spec (hits e h)
  have inj : Set.InjOn rep M := by
    intro e he f hf eq
    by_contra ne
    exact Finset.disjoint_left.mp (matching e he f hf ne)
      (Sym2.mem_toFinset.mpr (spec e he).1) (eq ▸ Sym2.mem_toFinset.mpr (spec f hf).1)
  have sub : M.image rep ⊆ S := by
    intro v hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    exact (spec e he).2
  simpa [Finset.card_image_of_injOn inj] using Finset.card_le_card sub

theorem matching_errors (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    {g : Nat} (hg : g ∈ junk graph C) (M : Finset Edge) (sub : M ⊆ Ustar graph C)
    (matching : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset)
    (first : ∀ e ∈ M, firstAt C g e) (sm : M.card ≤ 5) :
    ∃ errors : Finset Edge, lower M.card ≤ errors.card ∧ ∀ u v : V, s(u,v) ∈ errors →
      PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ (pairInput u v) = false ∧
      gateVal 11 C g (pairInput u v) = true := by
  apply gate_bound C least.1 hg _ _ sm
  intro b
  apply matching_hits M _ matching
  intro e he
  obtain ⟨j,hj,sides⟩ := first_hits C least top e (sub he)
  exact unique_first C e hj (first e he) ▸ sides b

end PEqualNP.Research.GateErrors6752

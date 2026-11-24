import Mathlib.Tactic
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Research.PlaneGatePrice

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireAccepts {p l} (C : Circuit) (w : ℕ) (P : Finset (Fin p)) (L : Finset (Fin l)) : Prop :=
  (C.wires (List.ofFn (Fin.append (fun a => decide (a ∈ P)) (fun b => decide (b ∈ L))))).getD w false = true

noncomputable def footprint (p l : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin p × Fin l) := by
  classical
  exact univ.filter fun e => wireAccepts C w {e.1} {e.2}

theorem wireAccepts_mono {p l} (C : Circuit) (hC : IsMonotoneCircuit C) (w : ℕ)
    {P P' : Finset (Fin p)} {L L' : Finset (Fin l)} (hp : P ⊆ P') (hl : L ⊆ L') :
    wireAccepts C w P L → wireAccepts C w P' L' := by
  apply LowMergeProof.wires_mono C hC _ _ (by simp) _ w
  intro i
  by_cases h : i < p+l
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
    let k : Fin (p+l) := ⟨i,h⟩
    change Fin.append _ _ k = true → Fin.append _ _ k = true
    induction k using Fin.addCases with
    | left a => simpa only [Fin.append_left,decide_eq_true_eq] using (fun hx => hp hx : a ∈ P → a ∈ P')
    | right b => simpa only [Fin.append_right,decide_eq_true_eq] using (fun hx => hl hx : b ∈ L → b ∈ L')
  · simp [List.getD_eq_getElem?_getD,h]


-- The indexed off-target pairs open the first operand. On any independent
-- input opening the other operand, each index must be hit across the two inputs.
theorem shared_frame_charge {p l m : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (mono : IsMonotoneCircuit C) (u v : Fin m → ℕ)
    (sound : ∀ i P L, wireAccepts C (u i) P L → wireAccepts C (v i) P L →
      ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E)
    (a : Fin m → Fin p) (b : Fin m → Fin l)
    (bad : ∀ i, (a i,b i) ∉ E ∧ wireAccepts C (u i) {a i} {b i})
    (r s : ℕ)
    (rowBound : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ r)
    (colBound : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ s)
    (P : Finset (Fin p)) (L : Finset (Fin l))
    (indep : ∀ x ∈ P, ∀ y ∈ L, (x,y) ∉ E) (accepted : ∀ i, wireAccepts C (v i) P L) :
    m ≤ P.card*r + L.card*s := by
  classical
  let row := fun x => univ.filter fun i => (x,b i) ∈ E
  let col := fun y => univ.filter fun i => (a i,y) ∈ E
  have covered : (univ : Finset (Fin m)) ⊆ P.biUnion row ∪ L.biUnion col := by
    intro i _
    obtain ⟨x,hx,y,hy,inc⟩ := sound i (insert (a i) P) (insert (b i) L)
      (wireAccepts_mono C mono (u i) (by simp) (by simp) (bad i).2)
      (wireAccepts_mono C mono (v i) (subset_insert _ _) (subset_insert _ _) (accepted i))
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · exact ((bad i).1 inc).elim
    · exact mem_union_right _ (mem_biUnion.mpr ⟨y,hy,by simpa [col] using inc⟩)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨x,hx,by simpa [row] using inc⟩)
    · exact (indep x hx y hy inc).elim
  calc
    m = (univ : Finset (Fin m)).card := by simp
    _ ≤ _ := card_le_card covered
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_biUnion_le.trans (sum_le_sum fun i _ => rowBound i))
      (card_biUnion_le.trans (sum_le_sum fun i _ => colBound i)) |>.trans (by simp)

-- Trace only wires required to keep a positive output true. A disjunction
-- needs one true predecessor, whereas a binary conjunction may need both.
def andGate (g : Gate) : Bool := match g.op with | .and => true | _ => false

theorem frontier_certificate {n : ℕ} (C : Circuit) (mono : Monotone2 C) (F : Finset ℕ)
    (x : Fin n → Bool) (on : ∀ w ∈ F, (C.wires (List.ofFn x)).getD w false = true) :
    ∃ T : Finset (Fin n), T.card ≤ C.gates.countP andGate + F.card ∧
      (∀ i ∈ T, x i = true) ∧
      ∀ y : Fin n → Bool, (∀ i ∈ T, y i = true) →
        ∀ w ∈ F, (C.wires (List.ofFn y)).getD w false = true := by
  classical
  let run (gs : List Gate) (y : Fin n → Bool) := (Circuit.mk gs 0).wires (List.ofFn y)
  have len (gs : List Gate) (z : List Bool) : ((Circuit.mk gs 0).wires z).length = z.length+gs.length := by
    induction gs generalizing z with
    | nil => simp [Circuit.wires]
    | cons g gs ih => change ((Circuit.mk gs 0).wires (z ++ [_])).length = _; rw [ih]; simp; omega
  have last (gs : List Gate) (g : Gate) (y : Fin n → Bool) (k : ℕ) :
      (run (gs++[g]) y).getD k false =
      if k=n+gs.length then g.op.eval (g.inputs.map fun i => (run gs y).getD i false)
      else (run gs y).getD k false := by
    simp only [run,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ((run gs y) ++ [_]).getD k false = if k=n+gs.length then _ else (run gs y).getD k false
    have length : (run gs y).length = n+gs.length := by simp [run,len]
    by_cases eq : k=n+gs.length
    · simp [eq,← length]
    · rw [ite_eq_right eq]
      by_cases lt : k < (run gs y).length
      · exact List.getD_append _ _ _ _ lt
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
  have cut (gs : List Gate) (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set _) ∧ g.inputs.length ≤ 2)
      (F : Finset ℕ) (yes : ∀ i ∈ F, (run gs x).getD i false = true) :
      ∃ T : Finset (Fin n), T.card ≤ gs.countP andGate + F.card ∧
      (∀ i ∈ T, x i = true) ∧ ∀ y : Fin n → Bool, (∀ i ∈ T, y i = true) →
        ∀ i ∈ F, (run gs y).getD i false = true := by
    induction gs using List.reverseRecOn generalizing F with
    | nil =>
      let T := univ.filter fun i : Fin n => i.val ∈ F
      have small : T.card ≤ F.card := card_le_card_of_injOn Fin.val
        (fun _ h => (mem_filter.mp h).2) (fun _ _ _ _ e => Fin.ext e)
      refine ⟨T,by simpa using small,?_,?_⟩
      · intro i hi
        simpa [run,Circuit.wires,List.getD_eq_getElem?_getD] using yes i (mem_filter.mp hi).2
      · intro y h k hk
        by_cases lt : k < n
        · simpa [run,Circuit.wires,List.getD_eq_getElem?_getD,lt] using h ⟨k,lt⟩ (by simpa [T] using hk)
        · have := yes k hk; simp [run,Circuit.wires,List.getD_eq_getElem?_getD,lt] at this
    | append_singleton gs g ih =>
      let k := n+gs.length
      have valid := ok g (by simp)
      have prev := fun a (ha : a ∈ gs) => ok a (by simp [ha])
      by_cases hk : k ∈ F
      · have out := yes k hk
        rw [last,ite_eq_left (show k=n+gs.length from rfl)] at out
        have choice : ∃ H : Finset ℕ, H.card ≤ (if andGate g then 2 else 1) ∧
            (∀ i ∈ H, (run gs x).getD i false = true) ∧
            ∀ y : Fin n → Bool, (∀ i ∈ H, (run gs y).getD i false = true) →
              g.op.eval (g.inputs.map fun i => (run gs y).getD i false) = true := by
          rcases valid.1 with op|op
          · refine ⟨g.inputs.toFinset,by simpa [andGate,op] using (List.toFinset_card_le (l := g.inputs)).trans valid.2,?_,?_⟩
            all_goals simp_all [GateOp.eval]
          · have hor : g.op = GateOp.or := op
            obtain ⟨j,hj,htrue⟩ : ∃ j ∈ g.inputs, (run gs x).getD j false = true := by
              simpa [hor,GateOp.eval] using out
            exact ⟨{j},by simp [andGate,hor],by simpa using htrue,fun y hy => by
              simpa [hor,GateOp.eval] using (show ∃ i ∈ g.inputs, (run gs y).getD i false = true from ⟨j,hj,hy j (by simp)⟩)⟩
        obtain ⟨H,hs,hy,eval⟩ := choice
        let G := F.erase k ∪ H
        have gx : ∀ i ∈ G, (run gs x).getD i false = true := by
          intro i hi
          rcases mem_union.mp hi with f|h
          · have hyes := yes i (mem_erase.mp f).2
            rw [last,ite_eq_right (show i ≠ n+gs.length from (mem_erase.mp f).1)] at hyes
            exact hyes
          · exact hy i h
        obtain ⟨T,tc,tx,det⟩ := ih prev G gx
        refine ⟨T,?_,tx,?_⟩
        · have := card_union_le (F.erase k) H
          have := card_erase_add_one hk
          simp only [List.countP_append,List.countP_singleton]
          dsimp [G] at tc
          split at hs <;> simp_all <;> omega
        · intro y h i hi
          rw [last]
          split
          · apply eval y
            exact fun j hj => det y h j (mem_union_right _ hj)
          · rename_i ne
            exact det y h i (mem_union_left _ (mem_erase.mpr ⟨ne,hi⟩))
      · have different (i) (hi : i ∈ F) : i ≠ n+gs.length := fun e => hk (by simpa only [k,← e] using hi)
        obtain ⟨T,tc,tx,det⟩ := ih prev F (fun i hi => by simpa only [last,ite_eq_right (different i hi)] using yes i hi)
        refine ⟨T,?_,tx,fun y h i hi => by simpa only [last,ite_eq_right (different i hi)] using det y h i hi⟩
        simp [List.countP_append]; omega
  exact cut C.gates mono F on

-- All sibling operands may share gates. On one common false assignment
-- their certificates together pay for every charge index.
theorem shared_gate_price {p l m : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (mono : Monotone2 C) (u v : Fin m → ℕ)
    (sound : ∀ i P L, wireAccepts C (u i) P L → wireAccepts C (v i) P L →
      ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E)
    (a : Fin m → Fin p) (b : Fin m → Fin l)
    (bad : ∀ i, (a i,b i) ∉ E ∧ wireAccepts C (u i) {a i} {b i})
    (d : ℕ) (rows : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ d)
    (cols : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ d)
    (P : Finset (Fin p)) (L : Finset (Fin l))
    (indep : ∀ x ∈ P, ∀ y ∈ L, (x,y) ∉ E) (accept : ∀ i, wireAccepts C (v i) P L) :
    m ≤ (C.gates.countP andGate + (univ.image v).card) * d := by
  classical
  let pos (S : Finset (Fin p)) (T : Finset (Fin l)) :=
    Fin.append (fun i => decide (i ∈ S)) (fun j => decide (j ∈ T))
  let F := univ.image v
  obtain ⟨K,size,inside,cert⟩ := frontier_certificate C mono F (pos P L) (by
    intro w hw; obtain ⟨i,_,rfl⟩ := mem_image.mp hw; exact accept i)
  let S := P.filter fun i => Fin.castAdd l i ∈ K
  let T := L.filter fun j => Fin.natAdd p j ∈ K
  let left : Fin p ↪ Fin (p+l) := ⟨Fin.castAdd l,Fin.castAdd_injective _ _⟩
  let right : Fin l ↪ Fin (p+l) := ⟨Fin.natAdd p,Fin.natAdd_injective _ _⟩
  have dis : Disjoint (S.map left) (T.map right) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i,_,rfl⟩ := mem_map.mp hz
    obtain ⟨j,_,eq⟩ := mem_map.mp hz'
    have hv := congrArg Fin.val eq
    change p+j.val = i.val at hv
    omega
  have sub : S.map left ∪ T.map right ⊆ K := by
    intro z hz
    rcases mem_union.mp hz with h|h
    · obtain ⟨i,hi,rfl⟩ := mem_map.mp h; exact (mem_filter.mp hi).2
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp h; exact (mem_filter.mp hj).2
  have small : S.card + T.card ≤ K.card := by
    simpa only [card_union_of_disjoint dis,card_map] using card_le_card sub
  have ones (k : Fin (p+l)) (hk : k ∈ K) : pos S T k = true := by
    have h := inside k hk
    induction k using Fin.addCases with
    | left i => simpa [pos,S,hk] using h
    | right j => simpa [pos,T,hk] using h
  have charges := shared_frame_charge E C (fun g hg => by simpa using (mono g hg).1)
    u v sound a b bad d d rows cols S T
    (fun x hx y hy => indep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1)
    (fun i => cert (pos S T) ones (v i) (mem_image_of_mem _ (mem_univ _)))
  rw [← Nat.add_mul] at charges
  exact charges.trans (Nat.mul_le_mul_right _ (small.trans size))

-- A least circuit cannot end in an AND if its second predecessor already
-- computes the whole graph. Consequently its negative witness exists without
-- any assumption on the internal form of that predecessor.
theorem final_and_price {p l m : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (mono : Monotone2 C) (u v : ℕ)
    (computes : ∀ P L, (wireAccepts C u P L ∧ wireAccepts C v P L) ↔
      ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E)
    (least : ∀ D : Circuit, Monotone2 D →
      (∀ P L, wireAccepts D D.output P L ↔ ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E) →
      C.size+1 ≤ D.size)
    (a : Fin m → Fin p) (b : Fin m → Fin l)
    (bad : ∀ i, (a i,b i) ∉ E ∧ wireAccepts C u {a i} {b i})
    (d : ℕ) (rows : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ d)
    (cols : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ d) :
    m ≤ (C.gates.countP andGate + 1) * d := by
  classical
  have counter : ∃ P L, wireAccepts C v P L ∧ ∀ x ∈ P, ∀ y ∈ L, (x,y) ∉ E := by
    by_contra! none
    let D : Circuit := ⟨C.gates,v⟩
    have cost := least D mono (by
      intro P L
      change wireAccepts C v P L ↔ _
      constructor
      · intro h; exact none P L h
      · intro h; exact ((computes P L).mpr h).2)
    change C.size+1 ≤ C.size at cost
    omega
  obtain ⟨P,L,on,indep⟩ := counter
  have bound := shared_gate_price E C mono (fun _ : Fin m => u) (fun _ => v)
    (fun _ P L h₁ h₂ => (computes P L).mp ⟨h₁,h₂⟩) a b bad d rows cols P L indep (fun _ => on)
  have one : (univ.image (fun _ : Fin m => v)).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨_,_,rfl⟩ := mem_image.mp hx
    obtain ⟨_,_,rfl⟩ := mem_image.mp hy
    rfl
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left one _))

-- In general position each row and column meets at most two selected pairs.
-- For four pairs, every opposite error determines a two-subset of the frame,
-- and the complementary two indices determine its other coordinate.
theorem four_pairs_six_errors {p l : ℕ} (E H : Finset (Fin p × Fin l))
    (thin : ∀ x z y w, x ≠ z → y ≠ w →
      ¬ ((x,y) ∈ E ∧ (x,w) ∈ E ∧ (z,y) ∈ E ∧ (z,w) ∈ E))
    (a : Fin 4 ↪ Fin p) (b : Fin 4 ↪ Fin l)
    (rows : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ 2)
    (cols : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ 2)
    (cross : ∀ e ∈ H, ∀ i, (e.1,b i) ∈ E ∨ (a i,e.2) ∈ E) :
    H.card ≤ 6 := by
  classical
  let R := fun x => univ.filter (fun i => (x,b i) ∈ E)
  let S := fun y => univ.filter (fun i => (a i,y) ∈ E)
  have cover (e) (he : e ∈ H) : (R e.1)ᶜ ⊆ S e.2 := by
    intro i hi
    have avoid : (e.1,b i) ∉ E := by simpa [R] using hi
    exact mem_filter.mpr ⟨mem_univ _,(cross e he i).resolve_left avoid⟩
  have two (e) (he : e ∈ H) : (R e.1).card = 2 ∧ (R e.1)ᶜ.card = 2 := by
    have h := card_compl_add_card (R e.1)
    have h₁ := card_le_card (cover e he)
    have h₂ := rows e.1
    have h₃ := cols e.2
    change (R e.1).card ≤ 2 at h₂
    change (S e.2).card ≤ 2 at h₃
    change (R e.1)ᶜ.card + (R e.1).card = 4 at h
    omega
  have injection : H.card ≤ ((univ : Finset (Fin 4)).powersetCard 2).card := by
    apply card_le_card_of_injOn (fun e => R e.1)
    · intro e he; exact mem_powersetCard.mpr ⟨subset_univ _,(two e he).1⟩
    · intro e he f hf same
      change R e.1 = R f.1 at same
      obtain ⟨i,j,hi,hj,ij⟩ := one_lt_card_iff.mp (show 1 < (R e.1).card by rw [(two e he).1]; decide)
      obtain ⟨k,t,hk,ht,kt⟩ := one_lt_card_iff.mp (show 1 < (R e.1)ᶜ.card by rw [(two e he).2]; decide)
      apply Prod.ext
      · by_contra diff
        exact thin _ _ _ _ diff (b.injective.ne ij)
          ⟨(mem_filter.mp hi).2,(mem_filter.mp hj).2,(mem_filter.mp (same ▸ hi : i ∈ R f.1)).2,
           (mem_filter.mp (same ▸ hj : j ∈ R f.1)).2⟩
      · by_contra diff
        exact thin _ _ _ _ (a.injective.ne kt) diff
          ⟨(mem_filter.mp (cover e he hk)).2,(mem_filter.mp (cover f hf (same ▸ hk))).2,
           (mem_filter.mp (cover e he ht)).2,(mem_filter.mp (cover f hf (same ▸ ht))).2⟩
  exact injection.trans (by decide +kernel)

-- A sharp ten-by-ten configuration in the affine chart over the field of
-- 199 elements. A line is stored as its slope and intercept.
def point : Fin 10 → ℕ × ℕ :=
  ![(0,0),(1,1),(2,4),(3,9),(198,11),(197,11),(196,11),(196,9),(195,8),(194,5)]
def line : Fin 10 → ℕ × ℕ :=
  ![(0,11),(1,12),(2,15),(3,20),(5,193),(4,196),(3,197),(3,0),(2,0),(1,0)]
def incident (x y : Fin 10) : Bool :=
  decide ((line y).1 * (point x).1 % 199 + (line y).2 ≡ (point x).2 [MOD 199])
def smallGraph := univ.filter (fun e : Fin 10 × Fin 10 => incident e.1 e.2)
def firstFour := (univ : Finset (Fin 4)).image fun i => (Fin.castAdd 6 i,Fin.castAdd 6 i)
def otherSix := (univ : Finset (Fin 6)).image fun i => (Fin.natAdd 4 i,Fin.natAdd 4 i)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sharp_table :
    (∀ x z y w : Fin 10, x ≠ z → y ≠ w →
      ¬ ((x,y) ∈ smallGraph ∧ (x,w) ∈ smallGraph ∧ (z,y) ∈ smallGraph ∧ (z,w) ∈ smallGraph)) ∧
    (∀ x : Fin 10, (univ.filter (fun i : Fin 4 => (x,Fin.castAdd 6 i) ∈ smallGraph)).card ≤ 2) ∧
    (∀ y : Fin 10, (univ.filter (fun i : Fin 4 => (Fin.castAdd 6 i,y) ∈ smallGraph)).card ≤ 2) ∧
    firstFour.card = 4 ∧ otherSix.card = 6 ∧ (∀ e ∈ firstFour, e ∉ smallGraph) ∧
    (∀ e ∈ otherSix, e ∉ smallGraph) ∧
    (∀ e ∈ firstFour, ∀ f ∈ otherSix, (e.1,f.2) ∈ smallGraph ∨ (f.1,e.2) ∈ smallGraph) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

def hit (E : Finset (Fin 10 × Fin 10)) (P L : Finset (Fin 10)) : Prop :=
  ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E

theorem sharp_on_every_input (P L : Finset (Fin 10)) :
    (hit (smallGraph ∪ firstFour) P L ∧ hit (smallGraph ∪ otherSix) P L) ↔ hit smallGraph P L := by
  constructor
  · rintro ⟨⟨x,hx,y,hy,inc⟩,⟨z,hz,w,hw,inc'⟩⟩
    rcases mem_union.mp inc with e|e
    · exact ⟨x,hx,y,hy,e⟩
    rcases mem_union.mp inc' with f|f
    · exact ⟨z,hz,w,hw,f⟩
    rcases sharp_table.2.2.2.2.2.2.2 _ e _ f with h|h
    · exact ⟨x,hx,w,hw,h⟩
    · exact ⟨z,hz,y,hy,h⟩
  · rintro ⟨x,hx,y,hy,e⟩
    exact ⟨⟨x,hx,y,hy,mem_union_left _ e⟩,⟨x,hx,y,hy,mem_union_left _ e⟩⟩

-- Every selected line contributes q+1 to the total row load. The frame
-- bound alone therefore cannot charge more than q+1 gates on a whole plane.
theorem incidence_ceiling {N q m d : ℕ} (E : Fin N → Fin N → Prop) [DecidableRel E]
    (order : N=q^2+q+1)
    (degree : ∀ j, (univ.filter fun x => E x j).card=q+1) (b : Fin m → Fin N)
    (rows : ∀ x, (univ.filter fun i => E x (b i)).card ≤ d) :
    m*(q+1) ≤ N*d ∧ m ≤ (q+1)*d := by
  have total : m*(q+1) ≤ N*d := calc
    m*(q+1) = ∑ i : Fin m, (univ.filter fun x => E x (b i)).card := by simp [degree]
    _ = ∑ i : Fin m, ∑ x : Fin N, if E x (b i) then 1 else 0 := by simp
    _ = ∑ x : Fin N, ∑ i : Fin m, if E x (b i) then 1 else 0 := sum_comm
    _ = ∑ x : Fin N, (univ.filter fun i => E x (b i)).card := by simp
    _ ≤ ∑ _ : Fin N, d := sum_le_sum (fun x _ => rows x)
    _ = N*d := by simp
  refine ⟨total,?_⟩
  have bound : N*d ≤ ((q+1)*d)*(q+1) := by
    calc
      N*d ≤ ((q+1)*(q+1))*d := Nat.mul_le_mul_right _ (by nlinarith [order])
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right (total.trans bound) (by omega)


theorem sound_and_six_errors {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (mono : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
      ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E)
    (thin : ∀ x z y w, x ≠ z → y ≠ w →
      ¬ ((x,y) ∈ E ∧ (x,w) ∈ E ∧ (z,y) ∈ E ∧ (z,w) ∈ E))
    (a : Fin 4 ↪ Fin p) (b : Fin 4 ↪ Fin l)
    (bad : ∀ i, (a i,b i) ∉ E ∧ wireAccepts C u {a i} {b i})
    (rows : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ 2)
    (cols : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ 2) :
    (footprint p l C v \ E).card ≤ 6 := by
  classical
  apply four_pairs_six_errors E _ thin a b rows cols
  intro e he i
  obtain ⟨hv,off⟩ := mem_sdiff.mp he
  have on := (mem_filter.mp hv).2
  obtain ⟨x,hx,y,hy,edge⟩ := sound ({a i,e.1} : Finset _) ({b i,e.2} : Finset _)
    (wireAccepts_mono C mono u (by simp) (by simp) (bad i).2)
    (wireAccepts_mono C mono v (by simp) (by simp) on)
  have miss := (bad i).1
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp_all

theorem five_force_pair_sound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (mono : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
      ∃ x ∈ P, ∃ y ∈ L, (x,y) ∈ E)
    (a : Fin 5 → Fin p) (b : Fin 5 → Fin l)
    (bad : ∀ i, (a i,b i) ∉ E ∧ wireAccepts C u {a i} {b i})
    (rows : ∀ x, (univ.filter (fun i => (x,b i) ∈ E)).card ≤ 2)
    (cols : ∀ y, (univ.filter (fun i => (a i,y) ∈ E)).card ≤ 2) :
    footprint p l C v ⊆ E := by
  classical
  intro e he
  by_contra off
  have bound := shared_frame_charge E C mono (fun _ : Fin 5 => u) (fun _ => v)
    (fun _ => sound) a b bad 2 2 rows cols {e.1} {e.2}
    (by simpa using off) (fun _ => (mem_filter.mp he).2)
  simp at bound

end PEqualNP.Research.PlaneGatePrice

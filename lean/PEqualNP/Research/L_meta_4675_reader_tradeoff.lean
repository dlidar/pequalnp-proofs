import PEqualNP.Research.L_meta_4675_star_networks

namespace PEqualNP.Research.ReaderTradeoff
open Finset PEqualNP.Research.StarNetworks PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def matching {p l} (H : Finset (Fin p × Fin l)) (m : ℕ) :=
  ∃ (a : Fin m → Fin p) (b : Fin m → Fin l), Function.Injective a ∧ Function.Injective b ∧
    ∀ i, (a i,b i) ∈ H

-- Code a column by one equal-colour pair among its three entries.
def code (x y z : Bool) : Fin 6 :=
  if x = y then (if x then 1 else 0)
  else if x = z then (if x then 3 else 2)
  else (if y then 5 else 4)
theorem code_rectangle : ∀ a b c x y z : Bool, code a b c = code x y z →
    (a=b ∧ b=x ∧ x=y) ∨ (a=c ∧ c=x ∧ x=z) ∨ (b=c ∧ c=y ∧ y=z) := by decide +kernel

theorem rectangle37 (M : Fin 3 → Fin 7 → Bool) :
    ∃ i k j m, i ≠ k ∧ j ≠ m ∧ M i j = M i m ∧ M i m = M k j ∧ M k j = M k m := by
  let f (j : Fin 7) := code (M 0 j) (M 1 j) (M 2 j)
  obtain ⟨j,m,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by decide)
  rcases code_rectangle _ _ _ _ _ _ eq with h|h|h
  · exact ⟨0,1,j,m,by decide,ne,h.1.trans h.2.1,h.2.1.symm,h.2.1.trans h.2.2⟩
  · exact ⟨0,2,j,m,by decide,ne,h.1.trans h.2.1,h.2.1.symm,h.2.1.trans h.2.2⟩
  · exact ⟨1,2,j,m,by decide,ne,h.1.trans h.2.1,h.2.1.symm,h.2.1.trans h.2.2⟩
theorem no_three_seven {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E) :
    ¬ (matching (F \ E) 3 ∧ matching (G \ E) 7) := by
  classical
  rintro ⟨⟨a,b,ia,ib,ab⟩,⟨c,d,ic,id',cd⟩⟩
  let M (i : Fin 3) (j : Fin 7) := decide ((a i,d j) ∈ E)
  have red (i j) (h : M i j = true) : (a i,d j) ∈ E := of_decide_eq_true h
  have blue (i j) (h : M i j = false) : (c j,b i) ∈ E := by
    obtain ⟨hab,nab⟩ := mem_sdiff.mp (ab i)
    obtain ⟨hcd,ncd⟩ := mem_sdiff.mp (cd j)
    exact (cross _ _ _ _ hab nab hcd ncd).resolve_left (of_decide_eq_false h)
  obtain ⟨i,k,j,m,ik,jm,s,t,u⟩ := rectangle37 M
  cases h : M i j with
  | true =>
    exact no4 _ _ _ _ (ia.ne ik) (id'.ne jm)
      ⟨red i j h,red i m (s ▸ h),red k j (t ▸ s ▸ h),red k m (u ▸ t ▸ s ▸ h)⟩
  | false =>
    exact no4 _ _ _ _ (ic.ne jm) (ib.ne ik)
      ⟨blue i j h,blue k j (t ▸ s ▸ h),blue i m (s ▸ h),blue k m (u ▸ t ▸ s ▸ h)⟩

theorem cover_of_no_matching {p l} (k : ℕ) (H : Finset (Fin p × Fin l)) (none : ¬matching H (k+1)) :
    smallCover H k := by
  classical
  by_contra noCover
  let N (i : Fin p) := univ.filter fun j : Fin l => (i,j) ∈ H
  have deficient (s : Finset (Fin p)) : k+1 ≤ p - s.card + (s.biUnion N).card := by
    by_contra! small
    apply noCover
    refine ⟨univ \ s,s.biUnion N,?_,?_⟩
    · simpa [card_sdiff_of_subset (subset_univ s)] using (show _ ≤ k by omega : p - s.card + (s.biUnion N).card ≤ k)
    · intro i j h
      by_cases hi : i ∈ s
      · exact Or.inr (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
      · exact Or.inl (by simpa using hi)
  have hp : k+1 ≤ p := by simpa using deficient ∅
  let T (i : Fin p) := (N i).disjSum (univ : Finset (Fin (p-(k+1))))
  have hall (s : Finset (Fin p)) : s.card ≤ (s.biUnion T).card := by
    rcases s.eq_empty_or_nonempty with rfl|⟨z,hz⟩
    · simp
    · have eq : s.biUnion T = (s.biUnion N).disjSum (univ : Finset (Fin (p-(k+1)))) := by
        ext v
        cases v with
        | inl j => simp [T]
        | inr d =>
          simp [T]
          exact ⟨z,hz⟩
      rw [eq,card_disjSum,card_univ,Fintype.card_fin]
      have := deficient s
      have hs : s.card ≤ p := by simpa using card_le_univ s
      omega
  obtain ⟨f,hf,member⟩ := (all_card_le_biUnion_card_iff_existsInjective' T).mp hall
  let U := univ.image f
  have size : U.card = p := by simp [U,card_image_of_injective _ hf]
  have cap : U.toRight.card ≤ p-(k+1) := by simpa using card_le_univ U.toRight
  have split : U.toLeft.card + U.toRight.card = U.card := card_toLeft_add_card_toRight
  have five : k+1 ≤ U.toLeft.card := by omega
  let b := U.toLeft.orderEmbOfCardLe five
  have pick (i : Fin (k+1)) : ∃ a, f a = Sum.inl (b i) := by
    have hit := mem_toLeft.mp (U.toLeft.orderEmbOfCardLe_mem five i)
    obtain ⟨a,_,ha⟩ := mem_image.mp hit
    exact ⟨a,ha⟩
  choose a ha using pick
  apply none
  refine ⟨a,b,?_,b.injective,?_⟩
  · intro i j same
    exact b.injective (Sum.inl.inj ((ha i).symm.trans ((congrArg f same).trans (ha j))))
  · intro i
    have h := member (a i)
    rw [ha] at h
    exact (mem_filter.mp (inl_mem_disjSum.mp h)).2


theorem tradeoff {p l} (E F G : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (cross : ∀ a b c d, (a,b) ∈ F → (a,b) ∉ E → (c,d) ∈ G → (c,d) ∉ E →
      (a,d) ∈ E ∨ (c,b) ∈ E) :
    smallCover (F \ E) 2 ∨ smallCover (G \ E) 2 ∨
    (smallCover (F \ E) 4 ∧ smallCover (G \ E) 6) ∨
    (smallCover (F \ E) 6 ∧ smallCover (G \ E) 4) := by
  by_cases f : matching (F \ E) 3
  swap
  · exact Or.inl (cover_of_no_matching 2 _ f)
  by_cases g : matching (G \ E) 3
  swap
  · exact Or.inr (Or.inl (cover_of_no_matching 2 _ g))
  have flip := fun c d a b hg ng hf nf => (cross a b c d hf nf hg ng).symm
  have G6 := cover_of_no_matching 6 _ (fun h => no_three_seven E F G no4 cross ⟨f,h⟩)
  have F6 := cover_of_no_matching 6 _ (fun h => no_three_seven E G F no4 flip ⟨g,h⟩)
  by_cases f5 : hasFiveMatching (F \ E)
  · exact Or.inr (Or.inr (Or.inr ⟨F6,four_cover_of_no_five _ (fun h => cross_matching_limit E F G no4 cross ⟨f5,h⟩)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨four_cover_of_no_five _ f5,G6⟩))

theorem reader_tradeoff {p l} (E : Finset (Fin p × Fin l)) (no4 : fourFree E)
    (C : Circuit) (hC : IsMonotoneCircuit C) (u v : ℕ)
    (sound : ∀ P L, wireAccepts C u P L → wireAccepts C v P L →
       ∃ a ∈ P, ∃ b ∈ L, (a,b) ∈ E) :
    let F := footprint p l C u \ E
    let G := footprint p l C v \ E
    smallCover F 2 ∨ smallCover G 2 ∨
      (smallCover F 4 ∧ smallCover G 6) ∨ (smallCover F 6 ∧ smallCover G 4) :=
  tradeoff E _ _ no4 (sound_wire_cross E C hC u v sound)

def safe {n m} (M : Fin n → Fin m → Bool) := ∀ i k j t, i ≠ k → j ≠ t →
    ¬(M i j = M i t ∧ M i t = M k j ∧ M k j = M k t)

def rel {n m} (M : Fin n → Fin m → Bool) : (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → Bool
  | .inl i,.inr j => M i j
  | .inr j,.inl i => !(M i j)
  | _,_ => false

theorem rel_thin {n m} (M : Fin n → Fin m → Bool) (h : safe M) (a c b d)
    (ac : a ≠ c) (bd : b ≠ d) : ¬(rel M a b ∧ rel M a d ∧ rel M c b ∧ rel M c d) := by
  cases a with
  | inl i =>
    cases c with
    | inr k => cases b <;> simp [rel]
    | inl k =>
      cases b with
      | inl j => simp [rel]
      | inr j =>
        cases d with
        | inl t => simp [rel]
        | inr t =>
          rintro ⟨a,b,c,d⟩
          exact h i k j t (fun e => ac (congrArg _ e)) (fun e => bd (congrArg _ e))
            ⟨a.trans b.symm,b.trans c.symm,c.trans d.symm⟩
  | inr j =>
    cases c with
    | inl t => cases b <;> simp [rel]
    | inr t =>
      cases b with
      | inr i => simp [rel]
      | inl i =>
        cases d with
        | inr k => simp [rel]
        | inl k =>
          simp only [rel,Bool.not_eq_true']
          rintro ⟨a,b,c,d⟩
          exact h i k j t (fun e => bd (congrArg _ e)) (fun e => ac (congrArg _ e))
            ⟨a.trans c.symm,c.trans b.symm,b.trans d.symm⟩

/-- Realize each safe colour matrix by two graph-valued operands. Both extra
sets are matchings and the AND is the target edge function on every input. -/
theorem realize {n m} (M : Fin n → Fin m → Bool) (safeM : safe M) :
    ∃ E F G : Finset (Fin (n+m) × Fin (n+m)), fourFree E ∧
    (∀ P L, (hits F P L ∧ hits G P L) ↔ hits E P L) ∧
    matching (F \ E) n ∧ matching (G \ E) m ∧
    smallCover (F \ E) n ∧ smallCover (G \ E) m := by
  classical
  let e : (Fin n ⊕ Fin m) ≃ Fin (n+m) := finSumFinEquiv
  let a (i : Fin n) := e (Sum.inl i)
  let b (j : Fin m) := e (Sum.inr j)
  have ia : Function.Injective a := fun _ _ h => Sum.inl.inj (e.injective h)
  have ib : Function.Injective b := fun _ _ h => Sum.inr.inj (e.injective h)
  let E := univ.filter (fun z : Fin (n+m) × Fin (n+m) => rel M (e.symm z.1) (e.symm z.2))
  let A := univ.image fun i => (a i,a i)
  let B := univ.image fun j => (b j,b j)
  have thin : fourFree E := by
    intro i k j t ik jt h
    simp only [E,mem_filter,mem_univ,true_and] at h
    exact rel_thin M safeM _ _ _ _ (e.symm.injective.ne ik) (e.symm.injective.ne jt) h
  have mem (i j : Fin n ⊕ Fin m) : (e i,e j) ∈ E ↔ rel M i j = true := by
    dsimp only [E]
    rw [mem_filter]
    simp only [mem_univ,true_and,Equiv.symm_apply_apply]
  have left (i) : (a i,a i) ∉ E := fun h => Bool.noConfusion ((mem _ _).mp h)
  have right (j) : (b j,b j) ∉ E := fun h => Bool.noConfusion ((mem _ _).mp h)
  have exactHits : ∀ P L, (hits (E ∪ A) P L ∧ hits (E ∪ B) P L) ↔ hits E P L := by
    intro P L
    constructor
    · rintro ⟨⟨x,y,hxy,hx,hy⟩,⟨u,v,huv,hu,hv⟩⟩
      rcases mem_union.mp hxy with h|h
      · exact ⟨x,y,h,hx,hy⟩
      rcases mem_union.mp huv with h'|h'
      · exact ⟨u,v,h',hu,hv⟩
      obtain ⟨i,_,eq⟩ := mem_image.mp h
      obtain ⟨j,_,eq'⟩ := mem_image.mp h'
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq.symm
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq'.symm
      cases hcol : M i j with
      | true => exact ⟨_,_,(mem (.inl i) (.inr j)).mpr hcol,hx,hv⟩
      | false => exact ⟨_,_,(mem (.inr j) (.inl i)).mpr (by simp [rel,hcol]),hu,hy⟩
    · rintro ⟨x,y,h,hx,hy⟩
      exact ⟨⟨x,y,mem_union_left _ h,hx,hy⟩,⟨x,y,mem_union_left _ h,hx,hy⟩⟩
  have cover {k : ℕ} (f : Fin k → Fin (n+m)) :
      smallCover ((E ∪ (univ.image fun i => (f i,f i))) \ E) k := by
    refine ⟨univ.image f,∅,by simpa using (card_image_le (s := univ) (f := f)),?_⟩
    intro x y h
    obtain ⟨i,hi,eq⟩ := mem_image.mp ((mem_union.mp (mem_sdiff.mp h).1).resolve_left (mem_sdiff.mp h).2)
    exact Or.inl (mem_image.mpr ⟨i,hi,congrArg Prod.fst eq⟩)
  exact ⟨E,E ∪ A,E ∪ B,thin,exactHits,
    ⟨a,a,ia,ia,fun i => mem_sdiff.mpr ⟨mem_union_right _ (mem_image_of_mem _ (mem_univ i)),left i⟩⟩,
    ⟨b,b,ib,ib,fun j => mem_sdiff.mpr ⟨mem_union_right _ (mem_image_of_mem _ (mem_univ j)),right j⟩⟩,
    cover a,cover b⟩

def sixCols (i : Fin 4) (j : Fin 6) : Bool := ([3,5,6,9,10,12] : List ℕ)[j.val]!.testBit i.val
theorem sixCols_safe : safe sixCols := by unfold safe; decide +kernel
theorem twoRows_safe (m : ℕ) : safe (fun (i : Fin 2) (_ : Fin m) => decide (i = 0)) := by
  intro i k j t ne _ h
  fin_cases i <;> fin_cases k <;> simp_all

def attainable (n m : ℕ) := ∃ E F G : Finset (Fin (n+m) × Fin (n+m)),
  fourFree E ∧ (∀ P L, (hits F P L ∧ hits G P L) ↔ hits E P L) ∧
  matching (F \ E) n ∧ matching (G \ E) m ∧ smallCover (F \ E) n ∧ smallCover (G \ E) m

theorem attainable_iff (n m : ℕ) : attainable n m ↔
    n ≤ 2 ∨ m ≤ 2 ∨ (n ≤ 4 ∧ m ≤ 6) ∨ (n ≤ 6 ∧ m ≤ 4) := by
  constructor
  · rintro ⟨E,F,G,thin,hits_eq,⟨a,b,ia,ib,ab⟩,⟨c,d,ic,id',cd⟩,_,_⟩
    have t := tradeoff E F G thin ((nested_and_exact E F G).mp hits_eq).2
    have hF := fun k => matching_le_cover (F \ E) (k := k) a b ia ib ab
    have hG := fun k => matching_le_cover (G \ E) (k := k) c d ic id' cd
    rcases t with h|h|⟨hf,hg⟩|⟨hf,hg⟩
    · exact Or.inl (hF 2 h)
    · exact Or.inr (Or.inl (hG 2 h))
    · exact Or.inr (Or.inr (Or.inl ⟨hF 4 hf,hG 6 hg⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hF 6 hf,hG 4 hg⟩))
  · have restrict {r s : ℕ} {M : Fin r → Fin s → Bool} (h : safe M) (nr : n ≤ r) (ms : m ≤ s) :
        safe (fun (i : Fin n) (j : Fin m) => M (i.castLE nr) (j.castLE ms)) := by
      intro i k j t ik jt
      apply h
      · exact (fun e => ik (Fin.ext (congrArg (Fin.val (n := r)) e)))
      · exact (fun e => jt (Fin.ext (congrArg (Fin.val (n := s)) e)))
    have flip {r s : ℕ} {M : Fin r → Fin s → Bool} (h : safe M) :
        safe (fun j i => M i j) := by
      intro j t i k jt ik ⟨ab,bc,cd⟩
      exact h i k j t ik jt ⟨ab.trans bc,bc.symm,bc.trans cd⟩
    rintro (n2|m2|⟨n4,m6⟩|⟨n6,m4⟩)
    · exact realize _ (restrict (twoRows_safe m) n2 le_rfl)
    · exact realize _ (restrict (flip (twoRows_safe n)) le_rfl m2)
    · exact realize _ (restrict sixCols_safe n4 m6)
    · exact realize _ (restrict (flip sixCols_safe) n6 m4)

end PEqualNP.Research.ReaderTradeoff

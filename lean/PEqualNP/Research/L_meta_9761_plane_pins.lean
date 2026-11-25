import PEqualNP.Research.L_meta_9761_plane_cut

/-!
# Point-line deletions

Translate the deleted point to index 20, then apply a checked incidence-preserving
permutation fixing 20 to normalize the line. The tables below give one such
permutation for every possible line. The last section retains a matching of
twenty edges to prove the sharp monotone cut width in either deletion case.
-/
namespace PEqualNP.Research.PlaneCut

private def pointMap : Array (Array (Fin 21)) := #[
  #[1,16,2,10,0,3,9,17,15,8,11,5,19,7,14,6,4,18,13,12,20],
  #[10,14,0,7,5,4,2,12,18,9,19,17,15,6,3,1,11,16,8,13,20],
  #[8,2,16,4,7,6,14,19,10,13,12,15,9,5,11,18,0,3,1,17,20],
  #[7,5,3,1,16,11,8,4,17,2,18,19,15,6,13,10,12,14,9,0,20],
  #[11,5,12,17,3,13,18,4,15,1,8,6,2,9,14,16,10,7,0,19,20],
  #[0,10,5,15,12,14,1,6,19,16,7,9,8,13,18,3,17,11,2,4,20],
  #[17,15,10,11,2,19,3,0,12,4,13,18,6,9,1,16,5,8,14,7,20],
  #[16,10,4,11,19,2,6,1,14,3,7,0,5,17,8,9,15,13,12,18,20],
  #[18,14,3,4,9,11,19,2,16,1,12,6,0,8,15,5,7,10,17,13,20],
  #[9,2,0,17,4,8,12,19,5,1,14,6,15,16,13,11,10,7,18,3,20],
  #[19,3,8,14,7,1,13,15,10,11,0,16,5,2,4,12,17,9,6,18,20],
  #[18,11,12,5,1,6,16,17,10,3,9,0,14,8,19,4,13,15,7,2,20],
  #[9,7,3,11,18,4,10,1,8,2,6,12,0,16,15,17,14,19,5,13,20],
  #[17,2,10,11,15,13,14,12,0,8,19,18,7,16,1,9,5,4,3,6,20],
  #[11,5,12,17,3,13,18,4,15,1,8,6,2,9,14,16,10,7,0,19,20],
  #[9,8,19,11,3,15,18,5,0,7,4,6,2,17,12,16,1,10,13,14,20],
  #[7,16,8,6,12,19,17,11,2,3,9,0,18,1,5,10,13,15,14,4,20],
  #[16,12,15,17,7,6,2,19,10,18,14,8,0,9,13,11,5,4,1,3,20],
  #[7,16,8,6,12,19,17,11,2,3,9,0,18,1,5,10,13,15,14,4,20],
  #[7,5,3,1,16,11,8,4,17,2,18,19,15,6,13,10,12,14,9,0,20],
  #[0,10,5,15,12,14,1,6,19,16,7,9,8,13,18,3,17,11,2,4,20]]
private def lineMap : Array (Array (Fin 21)) := #[
  #[0,2,9,17,20,8,16,1,15,7,10,5,3,14,13,11,4,18,12,19,6],
  #[10,0,7,12,4,9,19,17,14,5,3,1,11,2,8,18,16,15,13,20,6],
  #[7,2,0,3,6,13,19,15,9,12,11,14,5,10,18,17,20,8,1,16,4],
  #[12,10,8,0,16,7,4,3,1,2,18,15,11,13,9,17,19,14,5,20,6],
  #[10,12,17,3,20,18,4,11,1,8,13,2,9,14,0,15,6,7,5,19,16],
  #[17,10,1,11,19,0,6,5,15,12,14,8,13,18,2,3,16,7,9,4,20],
  #[1,15,10,7,19,3,20,17,11,9,18,2,5,8,0,12,4,13,14,6,16],
  #[15,9,11,18,19,2,6,0,10,3,7,5,1,13,8,14,20,12,17,4,16],
  #[14,10,3,9,16,18,19,2,0,8,11,5,7,15,1,12,6,17,13,20,4],
  #[9,7,17,3,4,8,19,5,1,0,13,11,15,12,18,10,6,14,2,20,16],
  #[3,8,13,14,6,18,20,15,10,7,0,12,1,9,11,17,16,5,2,4,19],
  #[18,11,12,1,6,2,16,17,10,8,5,0,13,15,3,9,20,14,7,19,4],
  #[14,3,10,18,4,9,6,8,7,2,11,17,0,15,1,13,19,5,12,20,16],
  #[1,9,10,11,20,13,19,17,7,15,18,14,12,0,8,5,4,3,2,6,16],
  #[10,12,17,3,20,18,4,11,1,8,13,2,9,14,0,15,6,7,5,19,16],
  #[8,15,18,10,20,14,4,5,7,3,11,2,1,17,12,0,6,9,13,19,16],
  #[12,15,13,11,19,3,16,7,2,8,5,17,18,1,10,9,20,14,0,4,6],
  #[12,11,1,3,6,2,19,15,17,14,13,7,5,9,18,10,4,0,8,20,16],
  #[12,15,13,11,19,3,16,7,2,8,5,17,18,1,10,9,20,14,0,4,6],
  #[12,10,8,0,16,7,4,3,1,2,18,15,11,13,9,17,19,14,5,20,6],
  #[17,10,1,11,19,0,6,5,15,12,14,8,13,18,2,3,16,7,9,4,20]]

private def pm (l i : Fin 21) : Fin 21 := (((pointMap[l.val]?).getD #[])[i.val]?).getD 0
private def lm (l i : Fin 21) : Fin 21 := (((lineMap[l.val]?).getD #[])[i.val]?).getD 0
private def shift (p i : Fin 21) : Fin 21 := Fin.ofNat 21 (20+(i.val+21-p.val))
private abbrev inc (p l : Fin 21) := l.val ∈ rows p.val

private theorem chart :
    (∀ j p l, inc (pm j p) (lm j l) ↔ inc p l) ∧
    (∀ j i : Fin 21, ∃ k, pm j k=i) ∧ (∀ j i : Fin 21, ∃ k, lm j k=i) ∧
    (∀ j, pm j 20=20) ∧ (∀ j, lm j j = if inc 20 j then 20 else 0) := by
  unfold inc; decide +kernel

private theorem rotations :
    (∀ a p l, inc (shift a p) (shift a l) ↔ inc p l) ∧
    (∀ a i : Fin 21, ∃ k, shift a k=i) ∧ (∀ a, shift a a=20) := by
  unfold inc; decide +kernel

/-- Every pinning of one point and one line has one of two canonical forms. -/
theorem move_pair (p l : Fin 21) :
    ∃ P L : Equiv.Perm (Fin 21), P p=20 ∧ L l=(if l.val ∈ rows p.val then 20 else 0) ∧
      ∀ i j, ((L j).val ∈ rows (P i).val ↔ j.val ∈ rows i.val) := by
  classical
  let j := shift p l
  have perm (f : Fin 21 → Fin 21) (s : Function.Surjective f) : Function.Bijective f :=
    ⟨(Finite.injective_iff_surjective).mpr s,s⟩
  let sh := Equiv.ofBijective (shift p) (perm _ (rotations.2.1 p))
  let P := sh.trans (Equiv.ofBijective (pm j) (perm _ (chart.2.1 j)))
  let L := sh.trans (Equiv.ofBijective (lm j) (perm _ (chart.2.2.1 j)))
  refine ⟨P,L,?_,?_,fun i k => (chart.1 j _ _).trans (rotations.1 p i k)⟩
  · change pm j (shift p p)=20
    rw [rotations.2.2,chart.2.2.2.1]
  · change lm j j = _
    rw [chart.2.2.2.2]
    have h := rotations.1 p p l
    rw [rotations.2.2] at h
    change (if inc 20 (shift p l) then _ else _) = _
    simp only [h,inc]

abbrev Side := Fin 21 → Bool

/-- Exact edge function after deleting point a and line b. -/
def pinned (a b : Fin 21) (x y : Side) : Bool := decide
  (∃ p l : Fin 21, p≠a ∧ l≠b ∧ l.val ∈ rows p.val ∧ x p=true ∧ y l=true)

theorem transport {a b c d : Fin 21} (P L : Equiv.Perm (Fin 21)) (ha : P a=c) (hb : L b=d)
    (geo : ∀ p l, (L l).val ∈ rows (P p).val ↔ l.val ∈ rows p.val)
    (x y : Side) :
    pinned a b x y = pinned c d (x ∘ P.symm) (y ∘ L.symm) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pinned,decide_eq_true_eq]
  constructor
  · rintro ⟨p,l,hp,hl,edge,hx,hy⟩
    exact ⟨P p,L l,fun h => hp (P.injective (h.trans ha.symm)),
      fun h => hl (L.injective (h.trans hb.symm)),(geo _ _).mpr edge,by simpa,by simpa⟩
  · rintro ⟨p,l,hp,hl,edge,hx,hy⟩
    refine ⟨P.symm p,L.symm l,?_,?_,?_,hx,hy⟩
    · intro he; exact hp ((P.apply_symm_apply p).symm.trans ((congrArg P he).trans ha))
    · intro he; exact hl ((L.apply_symm_apply l).symm.trans ((congrArg L he).trans hb))
    · apply (geo _ _).mp; simpa

def extSide (x : Side) (i : Nat) := x (Fin.ofNat 21 i)

theorem canonical_posted (l : Fin 21) (x y : Nat → Bool) :
    posted (input 20 [l.val] x y) = pinned 20 l (fun i => x i.val) (fun i => y i.val) := by
  apply Bool.eq_iff_iff.mpr
  rw [posted_restricted (by decide : 20≤21)]
  simp only [pinned,decide_eq_true_eq,neighborhood_bit,List.mem_singleton]
  constructor
  · rintro ⟨j,hj,ne,⟨i,hi,hx,e⟩,hy⟩
    refine ⟨⟨i,by omega⟩,⟨j,hj⟩,?_,?_,e,hx,hy⟩
    · intro h; have := congrArg Fin.val h; change i=20 at this; omega
    · intro h; exact ne (congrArg Fin.val h)
  · rintro ⟨i,j,hi,hj,e,hx,hy⟩
    have lt : i.val<20 := by
      have ne : i.val≠20 := fun h => hi (Fin.ext h); omega
    exact ⟨j,j.isLt,fun he => hj (Fin.ext he),⟨i,lt,hx,e⟩,hy⟩

def admits (f : Side → Side → Bool) (b : Nat) :=
  ∃ (encode : Side → (Fin b → Bool)) (decode : (Fin b → Bool) → Side → Bool),
    ∀ x y, f x y = decode (encode x) y

private theorem canonical_width (l : Fin 21) (b : Nat) :
    admits (pinned 20 l) b ↔ (messages 20 [l.val]).card ≤ 2^b := by
  rw [←binary_width (by decide : 20≤21) [l.val] (by simp)]
  constructor
  · rintro ⟨en,de,ok⟩
    exact ⟨fun x => en (fun i => x i.val),fun m y => de m (fun i => y i.val),
      fun x y => (canonical_posted l x y).trans (ok _ _)⟩
  · rintro ⟨en,de,ok⟩
    refine ⟨fun x => en (extSide x),fun m y => de m (extSide y),?_⟩
    intro x y
    have h := (canonical_posted l (extSide x) (extSide y)).symm.trans (ok _ _)
    simpa [extSide] using h

/-- After any point and line are pinned false, a one-way protocol exists precisely
above the relevant message threshold. Incident pins require 14 bits and
nonincident pins require 15. -/
theorem all_pinned_widths (a b : Fin 21) (k : Nat) :
    admits (pinned a b) k ↔ (if b.val ∈ rows a.val then 15959 else 16870) ≤ 2^k := by
  classical
  obtain ⟨P,L,hp,hl,geo⟩ := move_pair a b
  let d : Fin 21 := if b.val ∈ rows a.val then 20 else 0
  have f := transport P L hp (show L b = d from hl) geo
  have eq : admits (pinned a b) k ↔ admits (pinned 20 d) k := by
    constructor
    · rintro ⟨en,de,ok⟩
      refine ⟨fun x => en (x ∘ P), fun m y => de m (y ∘ L),?_⟩
      intro x y
      have h := (f (x ∘ P) (y ∘ L)).symm.trans (ok _ _)
      simpa [Function.comp_assoc] using h
    · rintro ⟨en,de,ok⟩
      exact ⟨fun x => en (x ∘ P.symm),fun m y => de m (y ∘ L.symm), fun x y => (f x y).trans (ok _ _)⟩
  rw [eq,canonical_width]
  by_cases edge : b.val ∈ rows a.val
  · simpa [d,edge] using (show (messages 20 [20]).card ≤ 2^k ↔ 15959 ≤ 2^k by rw [delete_incident_count])
  · simpa [d,edge] using (show (messages 20 [0]).card ≤ 2^k ↔ 16870 ≤ 2^k by rw [delete_nonincident_count])

private def mates (d : Fin 21) (i : Fin 20) : Fin 21 :=
  if d=20 then i.castSucc else
    (#[17,18,2,20,9,10,5,12,8,16,6,7,11,13,19,14,15,1,4,3] : Array (Fin 21))[i.val]!

private theorem mate_certificate : ∀ d : Fin 21, d=0 ∨ d=20 →
    (∀ i : Fin 20, mates d i ≠ d ∧ inc i.castSucc (mates d i)) ∧
    ∀ i j : Fin 20, i≠j → ¬(inc i.castSucc (mates d j) ∧ inc j.castSucc (mates d i)) := by
  unfold inc; decide +kernel

/-- A separating diagonal matching of twenty incidences survives every mixed deletion. -/
theorem surviving_matching (a b : Fin 21) :
    ∃ X Y : Fin 20 → Fin 21, (∀ i, X i ≠ a ∧ Y i ≠ b ∧ (Y i).val ∈ rows (X i).val) ∧
    ∀ i j, i≠j → ¬((Y j).val ∈ rows (X i).val ∧ (Y i).val ∈ rows (X j).val) := by
  obtain ⟨P,L,ha,hb,geo⟩ := move_pair a b
  let d := L b
  have alt : d=0 ∨ d=20 := by dsimp [d]; rw [hb]; split <;> simp
  obtain ⟨diag,cross⟩ := mate_certificate d alt
  refine ⟨fun i => P.symm i.castSucc,fun i => L.symm (mates d i),?_,?_⟩
  · intro i
    refine ⟨?_,?_,(geo _ _).mp (by simpa [inc] using (diag i).2)⟩
    · intro e
      have h := (P.apply_symm_apply i.castSucc).symm.trans ((congrArg P e).trans ha)
      have hv := congrArg Fin.val h
      change i.val=20 at hv
      omega
    · intro e
      exact (diag i).1 ((L.apply_symm_apply _).symm.trans (congrArg L e))
  · intro i j ne h
    apply cross i j ne
    exact ⟨by simpa [inc] using (geo _ _).mpr h.1,by simpa [inc] using (geo _ _).mpr h.2⟩

theorem pinned_monotone_lower (a b : Fin 21) {k}
    (en : Side → (Fin k → Bool)) (de : (Fin k → Bool) → Side → Bool)
    (ok : ∀ x y, pinned a b x y = de (en x) y)
    (me : Monotone en) (md : ∀ y, Monotone (fun v => de v y)) : 20 ≤ k := by
  obtain ⟨X,Y,diag,cross⟩ := surviving_matching a b
  let single (p : Fin 21) : Side := fun i => decide (i=p)
  let away (l : Fin 21) : Side := fun i => decide (l.val ∉ rows i.val)
  have yes (i : Fin 20) : pinned a b (single (X i)) (single (Y i)) = true :=
    decide_eq_true ⟨_,_,(diag i).1,(diag i).2.1,(diag i).2.2,by simp [single],by simp [single]⟩
  have no (l : Fin 21) : pinned a b (away l) (single l) = false := by
    simp [pinned,away,single]
  have existsBit (i : Fin 20) : ∃ j, en (single (X i)) j = true ∧ en (away (Y i)) j = false := by
    by_contra! bad
    have le : en (single (X i)) ≤ en (away (Y i)) := by
      intro j; apply Bool.le_iff_imp.mpr; intro h
      simpa using bad j h
    have h := md (single (Y i)) le
    change de (en (single (X i))) _ ≤ de (en (away (Y i))) _ at h
    rw [←ok,←ok,yes,no] at h
    exact (by decide : ¬true≤false) h
  choose j hi lo using existsBit
  have edge (p l : Fin 20) (e : j p=j l) : (Y l).val ∈ rows (X p).val := by
    by_contra miss
    have le : single (X p) ≤ away (Y l) := by
      intro w; by_cases h : w=X p <;> simp [single,away,h,miss]
    have val := me le (j l)
    rw [←e,hi,e,lo] at val
    exact (by decide : ¬true≤false) val
  have inj : Function.Injective j := by
    intro i q h
    by_contra ne
    exact cross i q ne ⟨edge i q h,edge q i h.symm⟩
  simpa using Fintype.card_le_of_injective _ inj

theorem pinned_monotone_upper (a b : Fin 21) :
    ∃ (en : Side → (Fin 20 → Bool)) (de : (Fin 20 → Bool) → Side → Bool),
      (∀ x y, pinned a b x y = de (en x) y) ∧ Monotone en ∧ ∀ y, Monotone (fun v => de v y) := by
  let en (x : Side) (i : Fin 20) := x (a.succAbove i)
  let de (m : Fin 20 → Bool) (y : Side) := decide (∃ i l, l≠b ∧ l.val ∈ rows (a.succAbove i).val ∧ m i=true ∧ y l=true)
  refine ⟨en,de,?_,fun _ _ h i => h (a.succAbove i),?_⟩
  · intro x y; apply Bool.eq_iff_iff.mpr
    simp only [pinned,de,decide_eq_true_eq,en]
    constructor
    · rintro ⟨p,l,ne,nb,e,hx,hy⟩
      obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq ne
      exact ⟨i,l,nb,e,hx,hy⟩
    · rintro ⟨i,l,nb,e,hx,hy⟩
      exact ⟨_,l,Fin.succAbove_ne _ _,nb,e,hx,hy⟩
  · intro y m m' le; apply Bool.le_iff_imp.mpr
    simp only [de,decide_eq_true_eq]
    rintro ⟨i,l,ne,e,hx,hy⟩
    exact ⟨i,l,ne,e,Bool.le_iff_imp.mp (le i) hx,hy⟩

end PEqualNP.Research.PlaneCut

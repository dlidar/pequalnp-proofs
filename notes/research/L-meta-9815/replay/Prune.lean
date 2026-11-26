import CachedBase
namespace PEqualNP.Research.Cached9815
abbrev Sub {V : Type*} (x y : V → Bool) := ∀ i,x i=true → y i=true
theorem sub_refl {V : Type*} (x : V → Bool) : Sub x x := fun _ h => h
theorem sub_trans {V : Type*} {x y z : V → Bool} (xy : Sub x y) (yz : Sub y z) : Sub x z :=
  fun i h => yz i (xy i h)
def left (r : Row) : EdgeInput := (#[0,0,1,1,1,2,2,3,3,3,4,4,4,5,5,5,6,6,6] : Array EdgeInput)[r.val]!
def right (r : Row) : EdgeInput := (#[8,10,7,9,13,8,13,7,11,12,10,11,13,9,10,12,8,9,11] : Array EdgeInput)[r.val]!

theorem row_support : ∀ r i,pos r i=(decide (i=left r) || decide (i=right r)) := by decide +kernel
theorem row_has (r : Row) (x : EdgeInput → Bool) (h : x (left r)=true ∧ x (right r)=true) : Sub (pos r) x := by
  intro i hi
  rw [row_support] at hi
  simp only [Bool.or_eq_true_iff,decide_eq_true_eq] at hi
  rcases hi with eq|eq
  · simpa [eq] using h.1
  · simpa [eq] using h.2
theorem positive_below (x : EdgeInput → Bool) (h : target x=true) : ∃ r, Sub (pos r) x := by
  simp only [target,Bool.or_eq_true_iff,Bool.and_eq_true_iff] at h
  rcases h with (((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · exact ⟨0,row_has 0 x h⟩
  · exact ⟨1,row_has 1 x h⟩
  · exact ⟨2,row_has 2 x h⟩
  · exact ⟨3,row_has 3 x h⟩
  · exact ⟨4,row_has 4 x h⟩
  · exact ⟨5,row_has 5 x h⟩
  · exact ⟨6,row_has 6 x h⟩
  · exact ⟨7,row_has 7 x h⟩
  · exact ⟨8,row_has 8 x h⟩
  · exact ⟨9,row_has 9 x h⟩
  · exact ⟨10,row_has 10 x h⟩
  · exact ⟨11,row_has 11 x h⟩
  · exact ⟨12,row_has 12 x h⟩
  · exact ⟨13,row_has 13 x h⟩
  · exact ⟨14,row_has 14 x h⟩
  · exact ⟨15,row_has 15 x h⟩
  · exact ⟨16,row_has 16 x h⟩
  · exact ⟨17,row_has 17 x h⟩
  · exact ⟨18,row_has 18 x h⟩

/-- External signals can be replaced by monotone alternatives whenever the alternatives
    agree on every minimal positive input and are below the originals everywhere. -/
theorem lower_advice {J : Type*} (d : (EdgeInput → Bool) → (J → Bool) → Bool)
    (mono : ∀ x y a b,Sub x y → Sub a b → d x a=true → d y b=true)
    (old newSig : (EdgeInput → Bool) → J → Bool)
    (smaller : ∀ x,Sub (newSig x) (old x))
    (grow : ∀ x y,Sub x y → Sub (newSig x) (newSig y))
    (agree : ∀ r,newSig (pos r)=old (pos r)) (correct : ∀ x,d x (old x)=target x) :
    ∀ x,d x (newSig x)=target x := by
  intro x
  cases eq : target x with
  | false =>
    cases h : d x (newSig x) with
    | false => rfl
    | true =>
      have hit := mono x x _ _ (sub_refl _) (smaller x) h
      rw [correct,eq] at hit
      contradiction
  | true =>
    obtain ⟨r,below⟩ := positive_below x eq
    have z : d (pos r) (newSig (pos r))=true := by rw [agree,correct,rows_ok]
    exact mono _ _ _ _ below (grow _ _ below) z

/-- Every external signal vanishing on the nineteen minimal positives may be discarded
    simultaneously when the remaining computation is monotone. -/
theorem discard_advice {J : Type*} (d : (EdgeInput → Bool) → (J → Bool) → Bool)
    (mono : ∀ x y a b,Sub x y → Sub a b → d x a=true → d y b=true)
    (old : (EdgeInput → Bool) → J → Bool) (silent : ∀ r j,old (pos r) j=false)
    (correct : ∀ x,d x (old x)=target x) : ∀ x,d x (fun _ => false)=target x := by
  apply lower_advice d mono old (fun _ _ => false)
  · intro x i h;contradiction
  · intro x y h;exact sub_refl _
  · intro r;funext j;exact (silent r j).symm
  · exact correct
theorem impossible_triple : ∀ r a b c,pos r a=true → pos r b=true → pos r c=true →
    a=b ∨ a=c ∨ b=c := by
  intro r a b c ha hb hc
  simp only [row_support,Bool.or_eq_true_iff,decide_eq_true_eq] at ha hb hc
  rcases ha with h|h <;> rcases hb with t|t <;> rcases hc with u|u <;> grind
theorem discard_triple_ands {J : Type*} (d : (EdgeInput → Bool) → (J → Bool) → Bool)
    (mono : ∀ x y a b,Sub x y → Sub a b → d x a=true → d y b=true)
    (a b c : J → EdgeInput) (ab : ∀ j,a j≠b j) (ac : ∀ j,a j≠c j) (bc : ∀ j,b j≠c j)
    (correct : ∀ x,d x (fun j => x (a j) && x (b j) && x (c j))=target x) :
    ∀ x,d x (fun _ => false)=target x := by
  apply discard_advice d mono _ _ correct
  intro r j
  cases h : (pos r (a j) && pos r (b j) && pos r (c j)) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true_iff] at h
    rcases impossible_triple _ _ _ _ h.1.1 h.1.2 h.2 with eq|eq|eq
    · exact (ab j eq).elim
    · exact (ac j eq).elim
    · exact (bc j eq).elim
end PEqualNP.Research.Cached9815

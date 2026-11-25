import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace PEqualNP.Research.SingleInverter

variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Row (α : Type*) := Finset α

def down (f : Row α → Bool) (x : Row α) := x.filter (fun i => f (x.erase i))
def up (f : Row α → Bool) (x : Row α) :=
  (Finset.univ \ x).filter (fun i => !f (insert i x))
def needed (f : Row α → Bool) (x : Row α) := if f x then down f x else up f x

def OnSlice (cut out : Row α → Bool) : Prop :=
  ∀ ⦃x y⦄, x ⊆ y → cut x = cut y → out x = true → out y = true

def OnSupport (cut : Row α → Bool) (s : Row α) : Prop :=
  ∀ ⦃x y⦄, (∀ i ∈ s, i ∈ x ↔ i ∈ y) → cut x = cut y

theorem tests_suffice (f cut out : Row α → Bool) (s : Row α)
    (hs : OnSupport cut s) (hm : OnSlice cut out)
    (checked : ∀ x, needed f x ⊆ s → out x = f x) : ∀ x, out x = f x := by
  have pos (x : Row α) : f x = true → out x = true := by
    induction x using Finset.strongInductionOn with
    | _ x ih =>
      intro hx
      by_cases h : down f x ⊆ s
      · exact (checked x (by simpa [needed,hx] using h)).trans hx
      · obtain ⟨i, hi, hnot⟩ := Finset.not_subset.mp h
        obtain ⟨hmem,hprev⟩ := Finset.mem_filter.mp hi
        apply hm (Finset.erase_subset i x) (hs ?_) (ih _ (Finset.erase_ssubset hmem) hprev)
        intro j hj
        have hji : j ≠ i := fun e => hnot (e ▸ hj)
        simp [hji]
  have neg (x : Row α) : f x = false → out x = false := by
    apply Finset.strongDownwardInduction (p := fun z => f z = false → out z = false) ?_ x (Finset.card_le_univ _)
    · intro x ih _ hx
      by_cases h : up f x ⊆ s
      · exact (checked x (by simpa [needed,hx] using h)).trans hx
      · obtain ⟨i,hi,hnot⟩ := Finset.not_subset.mp h
        obtain ⟨hmem,hnext⟩ := Finset.mem_filter.mp hi
        have hix := (Finset.mem_sdiff.mp hmem).2
        have hn : f (insert i x) = false := by simpa using hnext
        have h0 := ih (Finset.card_le_univ _) (Finset.ssubset_insert hix) hn
        cases ho : out x with
        | false => rfl
        | true =>
          have he := hm (Finset.subset_insert i x) (hs (by
            intro j hj
            have hji : j ≠ i := fun e => hnot (e ▸ hj)
            simp [hji])) ho
          simp [h0] at he
  intro x
  cases h : f x
  · exact neg x h
  · exact pos x h

def posCut (f : Row α → Bool) (x y : Row α) : Bool := decide (down f x ⊆ y)
def negCut (f : Row α → Bool) (x y : Row α) : Bool := decide (¬ Disjoint (up f x) y)
def dropAt (f : Row α → Bool) (x y : Row α) : Bool :=
  f y && (!posCut f x y || decide (¬ y ⊆ x))
def addAt (f : Row α → Bool) (x y : Row α) : Bool :=
  f y || (decide (x ⊆ y) && !negCut f x y)

theorem drop_exact (f : Row α → Bool) (mono : Monotone f) (x y : Row α) :
    dropAt f x y = (f y && decide (y ≠ x)) := by
  by_cases hy : y = x
  · subst y
    simp [dropAt,posCut,down,Finset.filter_subset]
  by_cases h : y ⊆ x
  · have w : ¬ x ⊆ y := fun e => hy (Finset.Subset.antisymm h e)
    obtain ⟨i,ix,iy⟩ := Finset.not_subset.mp w
    have he : y ⊆ x.erase i := fun j hj =>
      Finset.mem_erase.mpr ⟨fun e => iy (e ▸ hj),h hj⟩
    cases hf : f y
    · simp [dropAt,hf]
    · have ht : f (x.erase i) = true := Bool.eq_true_of_true_le (hf ▸ mono he)
      have hd : ¬ down f x ⊆ y := fun e => iy (e (Finset.mem_filter.mpr ⟨ix,ht⟩))
      simp [dropAt,posCut,hf,hd,hy]
  · simp [dropAt,h,hy]

theorem add_exact (f : Row α → Bool) (mono : Monotone f) (x y : Row α) :
    addAt f x y = (f y || decide (y = x)) := by
  by_cases hy : y = x
  · subst y
    have h : Disjoint (up f x) x := Finset.disjoint_left.mpr (fun i hi hx =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2 hx)
    simp [addAt,negCut,h]
  by_cases h : x ⊆ y
  · obtain ⟨i,iy,ix⟩ := Finset.not_subset.mp (show ¬ y ⊆ x from fun e => hy (Finset.Subset.antisymm e h))
    have he : insert i x ⊆ y := Finset.insert_subset iy h
    cases hf : f y
    · have ht : f (insert i x) = false := Bool.eq_false_of_le_false (hf ▸ mono he)
      have hu : i ∈ up f x := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ix⟩,by simp [ht]⟩
      have hd : ¬ Disjoint (up f x) y := fun e => Finset.disjoint_left.mp e hu iy
      simp [addAt,negCut,hf,hd,hy]
    · simp [addAt,hf]
  · simp [addAt,h,hy]

theorem pos_support (f : Row α → Bool) (x : Row α) :
    OnSupport (posCut f x) (down f x) := by
  intro y z h
  simp only [posCut,decide_eq_decide]
  exact ⟨fun a i hi => (h i hi).mp (a hi),fun a i hi => (h i hi).mpr (a hi)⟩

theorem neg_support (f : Row α → Bool) (x : Row α) :
    OnSupport (negCut f x) (up f x) := by
  intro y z h
  simp only [negCut,decide_eq_decide]
  simp only [Finset.disjoint_left]
  grind

theorem pos_mono (f : Row α → Bool) (x : Row α) : Monotone (posCut f x) := by
  intro y z hy
  simp only [posCut, Bool.le_iff_imp, decide_eq_true_eq]
  exact fun h => h.trans hy

theorem neg_mono (f : Row α → Bool) (x : Row α) : Monotone (negCut f x) := by
  intro y z hy
  simp only [negCut, Bool.le_iff_imp, decide_eq_true_eq]
  exact fun h d => h (Disjoint.mono_right hy d)

theorem drop_slice (f : Row α → Bool) (h : Monotone f) (x : Row α) :
    OnSlice (posCut f x) (dropAt f x) := by
  intro y z hy he
  simp only [dropAt,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,he]
  intro ⟨fy,hr⟩
  exact ⟨Bool.eq_true_of_true_le (fy ▸ h hy),hr.imp_right (fun p e => p (hy.trans e))⟩

theorem add_slice (f : Row α → Bool) (h : Monotone f) (x : Row α) :
    OnSlice (negCut f x) (addAt f x) := by
  intro y z hy he
  simp only [addAt,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,he]
  exact Or.imp (fun fy => Bool.eq_true_of_true_le (fy ▸ h hy))
    (fun ⟨hxy,hc⟩ => ⟨hxy.trans hy,hc⟩)

def Sufficient (f : Row α → Bool) (tests : Row α → Prop) (k : ℕ) : Prop :=
  ∀ (cut out : Row α → Bool) (s : Row α), s.card ≤ k → Monotone cut →
    OnSupport cut s → OnSlice cut out →
    (∀ y, tests y → out y = f y) → ∀ y, out y = f y

theorem sharp_tests (f : Row α → Bool) (h : Monotone f) (tests : Row α → Prop) (k : ℕ) :
    Sufficient f tests k ↔ ∀ x, (needed f x).card ≤ k → tests x := by
  constructor
  · intro all x hx
    by_contra omitted
    cases fx : f x with
    | false =>
      have fail := all (negCut f x) (addAt f x) (up f x) (by simpa [needed,fx] using hx)
        (neg_mono f x) (neg_support f x) (add_slice f h x) (by
          intro y hy
          have ne : y ≠ x := fun e => omitted (e ▸ hy)
          simp [add_exact f h x y,ne]) x
      simp [add_exact f h x x,fx] at fail
    | true =>
      have fail := all (posCut f x) (dropAt f x) (down f x) (by simpa [needed,fx] using hx)
        (pos_mono f x) (pos_support f x) (drop_slice f h x) (by
          intro y hy
          have ne : y ≠ x := fun e => omitted (e ▸ hy)
          simp [drop_exact f h x y,ne]) x
      simp [drop_exact f h x x,fx] at fail
  · intro cover cut out s size _ hs hm agree
    exact tests_suffice f cut out s hs hm (fun x hx => agree x (cover x ((Finset.card_le_card hx).trans size)))

end PEqualNP.Research.SingleInverter

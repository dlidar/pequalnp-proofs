import Order
namespace PinPrefix
open Finset
variable {α : Type*} [DecidableEq α]
def below (S : Finset α) (f : α → ℕ) (v : ℕ) := (S.filter (fun x => f x < v)).card
def bucket (S : Finset α) (f : α → ℕ) (w b : ℕ) :=
  (S.filter (fun x => w*b ≤ f x ∧ f x < w*(b+1))).card
theorem split_at (S : Finset α) (f : α → ℕ) {u v : ℕ} (hu : u ≤ v) :
    below S f v = below S f u + (S.filter (fun x => u ≤ f x ∧ f x < v)).card := by
  classical
  unfold below
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_union,mem_filter]
    by_cases hx : x ∈ S <;> simp_all <;> omega
  · simp only [Finset.disjoint_left, mem_filter]
    omega
theorem step (S : Finset α) (f : α → ℕ) (w b : ℕ) :
    below S f (w*(b+1)) = below S f (w*b) + bucket S f w b :=
  split_at S f (Nat.mul_le_mul_left w (by omega))
theorem radix3 (S : Finset α) (f : α → ℕ) (w b : ℕ) :
    bucket S f (3*w) b = bucket S f w (3*b) + bucket S f w (3*b+1) + bucket S f w (3*b+2) := by
  have h := step S f (3*w) b
  have e0 := step S f w (3*b)
  have e1 := step S f w (3*b+1)
  have e2 := step S f w (3*b+2)
  rw [show 3*w*(b+1) = w*(3*b+2+1) by ring, show 3*w*b = w*(3*b) by ring] at h
  rw [show 3*b+1+1=3*b+2 by omega] at e1
  omega
theorem digit_offset (S : Finset α) (f : α → ℕ) (w b : ℕ) (d : Fin 3) :
    below S f (w*(3*b+d.val)) = below S f ((3*w)*b) +
      (if 0 < d.val then bucket S f w (3*b) else 0) +
      (if 1 < d.val then bucket S f w (3*b+1) else 0) := by
  rw [show 3*w*b=w*(3*b) by ring]
  have h0 := step S f w (3*b)
  have h1 := step S f w (3*b+1)
  fin_cases d <;> simp_all
def choose (a b q : ℕ) : Fin 3 := if q < a then 0 else if q < a+b then 1 else 2
theorem select_step (S : Finset α) (f : α → ℕ) (w b q : ℕ)
    (hq : q < bucket S f (3*w) b) :
    let a := bucket S f w (3*b)
    let c := bucket S f w (3*b+1)
    let d := choose a c q
    let skip := (if 0 < d.val then a else 0) + (if 1 < d.val then c else 0)
    skip ≤ q ∧ q-skip < bucket S f w (3*b+d.val) ∧
      below S f ((3*w)*b)+q = below S f (w*(3*b+d.val))+(q-skip) := by
  dsimp only
  rw [radix3] at hq
  rw [digit_offset]
  unfold choose
  split_ifs <;> simp_all <;> omega
theorem ord_is_rank (S : Finset α) (f : α → ℕ) (e : Fin S.card ≃ {x // x ∈ S})
    (hs : ∀ i j, i < j → f (e i) < f (e j)) (i : Fin S.card) :
    below S f (f (e i)) = i.val := by
  classical
  have h : (S.filter (fun x => f x < f (e i))) =
      (Iio i).image (fun j => (e j).val) := by
    ext x
    simp only [mem_filter, mem_image, mem_Iio]
    constructor
    · rintro ⟨hx,lt⟩
      obtain ⟨j,hj⟩ := e.surjective ⟨x,hx⟩
      refine ⟨j,?_,congrArg Subtype.val hj⟩
      by_contra! bad
      have hxj : (e j).val = x := congrArg Subtype.val hj
      rw [← hxj] at lt
      exact (not_lt_of_ge ((show StrictMono (fun k => f (e k)) from fun _ _ h => hs _ _ h).monotone bad)) lt
    · rintro ⟨j,lt,rfl⟩
      exact ⟨(e j).2,hs _ _ lt⟩
  have inj : Function.Injective (fun j => (e j).val) := Subtype.val_injective.comp e.injective
  rw [below,h,Finset.card_image_of_injective _ inj,Fin.card_Iio]

def selectKey (counts : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,b,_ => b
  | j+1,b,q =>
    let a := counts (3^j) (3*b)
    let c := counts (3^j) (3*b+1)
    let d := choose a c q
    let skip := (if 0 < d.val then a else 0) + (if 1 < d.val then c else 0)
    selectKey counts j (3*b+d.val) (q-skip)
theorem select_invariant (S : Finset α) (f : α → ℕ) (hf : Function.Injective f)
    (j b q : ℕ) (hq : q < bucket S f (3^j) b) :
    ∃ x ∈ S, f x = selectKey (bucket S f) j b q ∧
      below S f (f x) = below S f (3^j*b)+q := by
  classical
  induction j generalizing b q with
  | zero =>
    simp only [pow_zero,one_mul] at *
    have pos : 0 < (S.filter (fun x => b ≤ f x ∧ f x < b+1)).card := by
      simpa [bucket] using (Nat.zero_lt_of_lt hq)
    obtain ⟨x,hx⟩ := Finset.card_pos.mp pos
    obtain ⟨hs,h1,h2⟩ := mem_filter.mp hx
    have eq : f x = b := by omega
    have unique : S.filter (fun y => b ≤ f y ∧ f y < b+1) = {x} := by
      ext y
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨_,ha,hb⟩; apply hf; omega
      · rintro rfl; exact ⟨hs,h1,h2⟩
    have k : bucket S f 1 b = 1 := by
      unfold bucket; simp only [one_mul]; rw [unique,card_singleton]
    have small : q < 1 := hq.trans_le k.le
    exact ⟨x,hs,eq,by rw [eq]; omega⟩
  | succ j ih =>
    rw [pow_succ'] at hq ⊢
    obtain ⟨_,hnext,hshift⟩ := select_step S f (3^j) b q hq
    obtain ⟨x,hx,he,hr⟩ := ih _ _ hnext
    exact ⟨x,hx,he,hr.trans hshift.symm⟩
theorem select_exact (S : Finset α) (f : α → ℕ) (hf : Function.Injective f)
    (digits : ℕ) (fits : ∀ x ∈ S, f x < 3^digits)
    (e : Fin S.card ≃ {x // x ∈ S}) (hs : ∀ i j, i < j → f (e i) < f (e j))
    (i : Fin S.card) : selectKey (bucket S f) digits 0 i.val = f (e i) := by
  classical
  have root : bucket S f (3^digits) 0 = S.card := by
    simp [bucket,Finset.filter_true_of_mem (fun x hx => fits x hx)]
  have hi : i.val < bucket S f (3^digits) 0 := i.isLt.trans_le root.ge
  obtain ⟨x,hx,he,hr⟩ := select_invariant S f hf digits 0 i.val hi
  obtain ⟨j,hj⟩ := e.surjective ⟨x,hx⟩
  have hd : (e j).val = x := congrArg Subtype.val hj
  have eqj := ord_is_rank S f e hs j
  rw [hd,hr] at eqj
  have ji : i=j := Fin.ext (by simpa [below] using eqj)
  simpa [ji,hd] using he.symm
end PinPrefix

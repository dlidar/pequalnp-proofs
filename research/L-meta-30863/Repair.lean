import Mathlib
namespace InverterRepair
open Finset
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Point (I : Type) := I → Bool

def Lower (f : Point I → Bool) (p : Point I) := f p=true ∧ ∀ x,x<p → f x=false
def Upper (f : Point I → Bool) (n : Point I) := f n=false ∧ ∀ x,n<x → f x=true

theorem lower_below {f : Point I → Bool} {x : Point I} (hx : f x=true) :
    ∃ p,p≤x ∧ Lower f p := by
  classical
  let s : Finset (Point I) := univ.filter (fun y => y≤x ∧ f y=true)
  obtain ⟨p,hp,minp⟩ := s.exists_minimal (show s.Nonempty from ⟨x,mem_filter.mpr ⟨mem_univ _,le_rfl,hx⟩⟩)
  obtain ⟨px,fp⟩ := (mem_filter.mp hp).2
  refine ⟨p,px,fp,fun y hy => ?_⟩
  by_contra! ne
  have fy := Bool.eq_true_of_not_eq_false ne
  exact hy.not_ge (minp (mem_filter.mpr ⟨mem_univ _,hy.le.trans px,fy⟩) hy.le)

theorem upper_above {f : Point I → Bool} {x : Point I} (hx : f x=false) :
    ∃ n,x≤n ∧ Upper f n := by
  classical
  let s : Finset (Point I) := univ.filter (fun y => x≤y ∧ f y=false)
  obtain ⟨n,hn,maxn⟩ := s.exists_maximal (show s.Nonempty from ⟨x,mem_filter.mpr ⟨mem_univ _,le_rfl,hx⟩⟩)
  obtain ⟨xn,fn⟩ := (mem_filter.mp hn).2
  refine ⟨n,xn,fn,fun y hy => ?_⟩
  by_contra! ne
  have fy := Bool.eq_false_of_not_eq_true ne
  exact hy.not_ge (maxn (mem_filter.mpr ⟨mem_univ _,xn.trans hy.le,fy⟩) hy.le)

theorem boundary_repair {f g b : Point I → Bool} (d : Point I → Bool → Bool)
    (dx : ∀ t, Monotone (fun x => d x t)) (dt : ∀ x, Monotone (d x)) (bm : Monotone b)
    (works : ∀ x,d x (!(g x))=f x)
    (pos : ∀ p,Lower f p → g p=false → b p=true)
    (neg : ∀ n,Upper f n → g n=true → b n=false) :
    ∀ x,d x (b x)=f x := by
  have dm : Monotone (fun x => d x (b x)) := fun x y xy => (dx (b x) xy).trans (dt y (bm xy))
  intro x
  cases h : f x with
  | true =>
    obtain ⟨p,hl,hp⟩ := lower_below h
    have le : (!(g p)) ≤ b p := by cases e : g p <;> simp [e, pos p hp]
    have e := (dt p le).trans (dm hl)
    rw [works,hp.1] at e
    exact le_antisymm le_top e
  | false =>
    obtain ⟨n,hl,hn⟩ := upper_above h
    have le : b n ≤ !(g n) := by cases e : g n <;> simp [e, neg n hn]
    have e := (dm hl).trans (dt n le)
    rw [works,hn.1] at e
    exact le_antisymm e bot_le
end InverterRepair

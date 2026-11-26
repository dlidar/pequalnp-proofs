import PEqualNP.Research.AffineMatrix
namespace PEqualNP.Research.AffineClique
open Finset PEqualNP.Research.AffineRectangleCover
abbrev Cell := P × L
def clash (x y : Cell) : Bool := !(zero x.1 y.2 && zero y.1 x.2)
def Clique (S : Finset Cell) := ∀ x∈S, ∀ y∈S, x ≠ y → clash x y
def branches (f : List Cell → Bool) : List Cell → Bool
  | [] => true
  | a::t => f (t.filter (clash a)) && branches f t
def cap : Nat → List Cell → Bool
  | 0,t => t.isEmpty
  | n+1,t => branches (cap n) t
theorem cap_sound (n : Nat) (t : List Cell) (h : cap n t = true) (S : Finset Cell)
    (hs : S ⊆ t.toFinset) (hc : Clique S) : S.card ≤ n := by
  induction n generalizing t S with
  | zero =>
    cases t with
    | nil => have hh : S=∅ := by simpa using hs
             simp [hh]
    | cons a t => contradiction
  | succ n ih =>
    induction t generalizing S with
    | nil => have hh : S=∅ := by simpa using hs
             simp [hh]
    | cons a t rec =>
      change (cap n (t.filter (clash a)) && branches (cap n) t) = true at h
      simp only [Bool.and_eq_true] at h
      by_cases ha : a∈S
      · have small := ih _ h.1 (S.erase a) (by
          intro x hx
          have v := hs (mem_of_mem_erase hx)
          have ne := ne_of_mem_erase hx
          have hx' : x∈t.toFinset := by simpa [List.toFinset_cons,ne] using v
          exact List.mem_toFinset.mpr <| List.mem_filter.mpr
            ⟨List.mem_toFinset.mp hx',hc a ha x (mem_of_mem_erase hx) ne.symm⟩)
          (fun x hx y hy => hc x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
        have eq := card_erase_add_one ha
        omega
      · exact rec h.2 S (fun x hx => by
          have ne : x ≠ a := fun he => ha (he ▸ hx)
          simpa [List.toFinset_cons,ne] using hs hx) hc

def origin : Cell := (0,1)
def pool : List Cell := (List.finRange 25).flatMap fun p =>
  ((List.finRange 30).map (fun l => (p,l))).filter (fun c => zero c.1 c.2 && clash origin c)
theorem in_pool (c : Cell) (hz : zero c.1 c.2) (conf : clash origin c) : c ∈ pool := by
  exact List.mem_flatMap.mpr ⟨c.1,List.mem_finRange _,List.mem_filter.mpr
    ⟨List.mem_map.mpr ⟨c.2,List.mem_finRange _,rfl⟩, by simp [hz,conf]⟩⟩
end PEqualNP.Research.AffineClique

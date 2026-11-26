import PEqualNP.Research.AffineSymmetry
import PEqualNP.Research.AffineCliqueCheck
import PEqualNP.Research.AffineFooling

namespace PEqualNP.Research.AffineClique
open Finset PEqualNP.Research.AffineRectangleCover PEqualNP.Research.AffineSymmetry
def center (x : P) := (#[[], [0, 3, 0], [3, 0], [0, 0], [0], [1, 0, 3, 0], [0, 3, 1, 2, 1, 0], [3, 1, 2, 1, 0], [0, 1, 2, 1, 0], [1, 2, 1, 0], [1, 3, 0], [2, 2, 1, 3, 0], [2, 0, 1, 3, 0], [2, 1, 3, 0], [0, 1, 3, 0], [1, 0, 0], [2, 0, 1, 0, 0], [2, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0], [1, 0], [2, 1, 0], [3, 0, 1, 0], [0, 0, 1, 0], [0, 1, 0]] : Array (List (Fin 4)))[x.val]!
def rotate (x : L) := (#[[], [], [3, 3, 3], [3], [3, 3], [], [2, 2, 2, 2], [1, 2, 3, 2], [2, 3, 2], [3, 3, 2], [], [2, 2, 2], [3, 2, 3, 3], [3, 2], [3, 2, 3], [], [2, 2], [1, 2, 2, 2], [2, 2, 3], [3, 2, 3, 2], [], [2], [2, 3, 3, 3], [2, 3], [2, 3, 3], [], [1], [1, 3, 3, 3], [1, 3], [1, 3, 3]] : Array (List (Fin 4)))[x.val]!

theorem center_point : ∀ p : P, move rowMap (center p) p = 0 := by decide +kernel
theorem rotate_origin : ∀ l : L, move rowMap (rotate l) 0 = 0 := by decide +kernel
theorem rotate_line : ∀ l : L, zero 0 l → move colMap (rotate l) l = 1 := by decide +kernel
def turn (gs : List (Fin 4)) (c : Cell) : Cell := (move rowMap gs c.1, move colMap gs c.2)
theorem turn_inj (gs : List (Fin 4)) : Function.Injective (turn gs) := by
  intro a b h
  have p := congrArg Prod.fst h
  have l := congrArg Prod.snd h
  exact Prod.ext ((move_inj rowMap (fun g _ _ => row_inj g _ _) gs) p) ((move_inj colMap (fun g _ _ => col_inj g _ _) gs) l)
theorem turn_clash (gs : List (Fin 4)) (a b : Cell) : clash (turn gs a) (turn gs b) = clash a b := by
  simp [turn,clash,move_zero]
theorem transport (c : Cell) (hz : zero c.1 c.2) : ∃ f : Cell → Cell,
    Function.Injective f ∧ f c = origin ∧ (∀ x,zero (f x).1 (f x).2 = zero x.1 x.2) ∧
    ∀ a b, clash (f a) (f b) = clash a b := by
  let gs := center c.1
  let l := move colMap gs c.2
  let t := rotate l
  have hp : move rowMap gs c.1 = 0 := center_point _
  have hl : zero 0 l = true := by
    rw [← hp]; exact (move_zero gs _ _).trans hz
  refine ⟨turn t ∘ turn gs,(turn_inj t).comp (turn_inj gs),?_,?_,?_⟩
  · apply Prod.ext
    · change move rowMap t (move rowMap gs c.1) = 0
      rw [hp];exact rotate_origin _
    · exact rotate_line l hl
  · intro x; exact (move_zero t _ _).trans (move_zero gs _ _)
  · intro a b; exact (turn_clash t _ _).trans (turn_clash gs _ _)

theorem fooling_upper (S : Finset Cell) (hz : ∀ x∈S, zero x.1 x.2) (hc : Clique S) : S.card ≤ 6 := by
  rcases S.eq_empty_or_nonempty with h | ⟨c,hc₀⟩
  · simp [h]
  obtain ⟨f,hinj,hor,hzero,hcl⟩ := transport c (hz c hc₀)
  let T := S.image f
  have hm : origin ∈ T := hor ▸ mem_image_of_mem f hc₀
  have hq : Clique T := by
    intro x hx y hy hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    exact (hcl a b).trans (hc a ha b hb (fun he => hn (congrArg f he)))
  have hsub : T.erase origin ⊆ pool.toFinset := by
    intro x hx
    have hm' := mem_of_mem_erase hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hm'
    exact List.mem_toFinset.mpr (in_pool (f a) ((hzero a).trans (hz a ha)) (hq origin hm _ hm' (ne_of_mem_erase hx).symm))
  have h := cap_sound _ _ origin_bound _ hsub (fun a ha b hb => hq a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
  have eq := card_erase_add_one hm
  have eq' : T.card = S.card := card_image_of_injective _ hinj
  omega

def six : Finset Cell := univ.image (fun i : Fin 6 => (PEqualNP.Research.AffineFooling.sixRow i, PEqualNP.Research.AffineFooling.sixCol i))
theorem six_size : six.card = 6 := by decide +kernel
theorem six_is_zero : ∀ x∈six, zero x.1 x.2 := by decide +kernel
theorem six_is_clique : Clique six := by unfold Clique; decide +kernel
end PEqualNP.Research.AffineClique

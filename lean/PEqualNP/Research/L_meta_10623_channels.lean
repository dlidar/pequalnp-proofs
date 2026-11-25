import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Tactic

namespace PEqualNP.Research.TriangleChannels
open PEqualNP.CircuitLowerBounds

abbrev Tri := Fin 3 → Bool
def high (x : Tri) := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
def low (x : Tri) := x 0 || x 1 || x 2
def f (x y : Tri) (c : Bool) := high x || high y || (c && (low x || low y))
def left (x : Fin 7 → Bool) : Tri := ![x 0,x 2,x 4]
def right (x : Fin 7 → Bool) : Tri := ![x 1,x 3,x 5]
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 10000 in
theorem exact_target : ∀ x, f (left x) (right x) (x 6) = target x := by decide +kernel

def ref : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 2]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [6, 17]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [18, 19]⟩],20⟩
theorem ref_size : ref.gates.length = 14 := rfl
theorem ref_legal : ∀ g ∈ ref.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [ref,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
theorem ref_exact : ∀ x, ref.eval (List.ofFn x) = target x := by decide +kernel

def profile (x : Tri) := (low x,high x)
def sufficient {β : Type*} (code : Tri → β) := ∀ x y, code x = code y → profile x = profile y
def empty : Tri := fun _ => false

theorem exact_messages (x y : Tri) :
    (∀ other c, f x other c = f y other c) ↔ profile x = profile y := by
  revert x y
  decide +kernel

theorem side_sufficient {β γ : Type*} (a : Tri → β) (b : Tri → γ) (dec : β → γ → Bool → Bool)
    (fits : ∀ x y c, dec (a x) (b y) c = f x y c) : sufficient a := by
  intro x y same
  apply (exact_messages x y).mp
  intro z c
  rw [←fits,←fits,same]

theorem no_single_bit (code : Tri → Bool) : ¬ sufficient code := by
  intro h
  let x : Tri := ![false,false,false]
  let y : Tri := ![true,false,false]
  let z : Tri := ![true,true,false]
  have sep (a b : Tri) (hh : profile a ≠ profile b) : code a ≠ code b := fun e => hh (h a b e)
  have h1 := sep x y (by decide +kernel)
  have h2 := sep x z (by decide +kernel)
  have h3 := sep y z (by decide +kernel)
  cases e : code x <;> cases j : code y <;> cases k : code z <;> simp_all

abbrev Pair := Bool × Bool
def zero : Tri := fun _ => false
def single (i : Fin 3) : Tri := fun j => decide (i = j)
def colored (color : Fin 3 → Bool) (x : Tri) : Pair :=
  (high x || (List.finRange 3).any (fun i => x i && color i),
   high x || (List.finRange 3).any (fun i => x i && !color i))

theorem color_valid : ∀ c : Fin 3 → Bool, sufficient (colored c) := by
  unfold sufficient
  decide +kernel

theorem color_mono : ∀ c : Fin 3 → Bool, Monotone (colored c) := by
  intro c x y le
  have finite : ∀ c x y : Tri, (∀ i, x i ≤ y i) →
      (colored c x).1 ≤ (colored c y).1 ∧ (colored c x).2 ≤ (colored c y).2 := by decide +kernel
  exact finite c x y le

theorem chain_codes (a b c : Pair) (less₁ : a ≤ b) (less₂ : b ≤ c) (ab : a ≠ b) (bc : b ≠ c) :
    a = (false,false) ∧ c = (true,true) ∧ b.2 = !b.1 := by
  rcases a with ⟨p,q⟩
  rcases b with ⟨r,s⟩
  rcases c with ⟨u,v⟩
  change p ≤ r ∧ q ≤ s at less₁
  change r ≤ u ∧ s ≤ v at less₂
  cases p <;> cases q <;> cases r <;> cases s <;> cases u <;> cases v <;> simp_all [Bool.le_iff_imp]

theorem classified (code : Tri → Pair) (valid : sufficient code) (mon : Monotone code) :
    code = colored (fun i => (code (single i)).1) := by
  have z (i : Fin 3) : zero ≤ single i := fun _ => Bool.false_le _
  let top : Tri := fun _ => true
  have pair_profile : ∀ i : Fin 3, profile (single i) ≠ profile top := by decide +kernel
  have zero_profile : ∀ i : Fin 3, profile zero ≠ profile (single i) := by decide +kernel
  have sig (i : Fin 3) := chain_codes (code zero) (code (single i)) (code top)
    (mon (z i)) (mon (fun j => Bool.le_true (single i j)))
    (fun e => zero_profile i (valid _ _ e)) (fun e => pair_profile i (valid _ _ e))
  have high_has : ∀ x : Tri, high x = true → ∃ i, single i ≤ x ∧ profile (single i) ≠ profile x := by
    change ∀ x : Tri, high x = true → ∃ i, (∀ j, single i j ≤ x j) ∧ profile (single i) ≠ profile x
    decide +kernel
  have basic : ∀ x : Tri, high x = false → x = zero ∨ ∃ i, x = single i := by decide +kernel
  have col0 : ∀ c, colored c zero = (false,false) := by decide +kernel
  have col1 : ∀ c i, colored c (single i) = (c i,!c i) := by decide +kernel
  funext x
  cases hx : high x
  · rcases basic x hx with rfl | ⟨i,rfl⟩
    · rw [col0]; exact (sig 0).1
    · rw [col1]; exact Prod.ext rfl (sig i).2.2
  · obtain ⟨i, hix, diff⟩ := high_has x hx
    have hi := (chain_codes _ _ _ (mon (z i)) (mon hix)
      (fun e => zero_profile i (valid _ _ e)) (fun e => diff (valid _ _ e))).2.1
    simpa [colored,hx] using hi

def split (c : Fin 3 → Bool) := ∃ i j, c i ≠ c j

theorem every_code : ∀ c : Fin 3 → Bool, split c → Function.Surjective (colored c) := by
  unfold split Function.Surjective
  decide +kernel

def bow (c : Bool) (a b : Pair) :=
  (a.1 && a.2) || (b.1 && b.2) || (c && (a.1 || a.2 || b.1 || b.2))

theorem bow_exact : ∀ ca cb x y c, bow c (colored ca x) (colored cb y) = f x y c := by decide +kernel

theorem decoder_forced (ca cb : Fin 3 → Bool) (ha : split ca) (hb : split cb)
    (dec : Pair → Pair → Bool → Bool)
    (fits : ∀ x y c, dec (colored ca x) (colored cb y) c = f x y c) :
    ∀ a b c, dec a b c = bow c a b := by
  intro a b c
  obtain ⟨x,rfl⟩ := every_code ca ha a
  obtain ⟨y,rfl⟩ := every_code cb hb b
  rw [fits,bow_exact]

end PEqualNP.Research.TriangleChannels

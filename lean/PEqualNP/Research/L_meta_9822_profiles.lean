import PEqualNP.Research.L_meta_9822_decoder
import PEqualNP.Defs

namespace PEqualNP.Research.PuncturedPetersen
open PEqualNP.Research.DecoderSlices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def edges : List (Nat × Nat) :=
  [(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
def target (x : Nat) : Bool := edges.any fun e => x.testBit e.1 && x.testBit e.2

def targetBits (x : Fin 10 → Bool) := (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem target_exact (m : Nat) : target m = targetBits (fun i => m.testBit i.val) := by
  simp [target,edges,targetBits,Bool.or_assoc]

theorem extend {x : Nat} (h : target x = true) (y : Nat) : target (x ||| y) = true := by
  obtain ⟨e,he,ab⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨e,he,?_⟩
  simp [Nat.testBit_or] at ab ⊢
  exact ⟨Or.inl ab.1,Or.inl ab.2⟩

def cofactor (p q x : Nat) : Table :=
  if target x then 15 else
  if target (x ||| 2^p) then (if target (x ||| 2^q) then 14 else 10)
  else if target (x ||| 2^q) then 12 else if target ((x ||| 2^p) ||| 2^q) then 8 else 0

theorem mono (p q x : Nat) : Mono (cofactor p q x) := by
  unfold cofactor
  split_ifs <;> decide

theorem four_entries (p q x : Nat) :
    let t := (cofactor p q x).val
    t.testBit 0 = target x ∧ t.testBit 1 = target (x ||| 2^p) ∧
    t.testBit 2 = target (x ||| 2^q) ∧ t.testBit 3 = target ((x ||| 2^p) ||| 2^q) := by
  have h0 := fun (h : target x = true) => And.intro (extend h (2^p)) (extend h (2^q))
  have h1 := fun (h : target (x ||| 2^p) = true) => extend h (2^q)
  have h2 : target (x ||| 2^q) = true → target ((x ||| 2^p) ||| 2^q) = true := by
    intro h; simpa [Nat.or_assoc,Nat.or_comm,Nat.or_left_comm] using extend h (2^p)
  dsimp only
  unfold cofactor
  split_ifs <;> simp_all <;> decide

def contexts (p q : Nat) := (List.range 1024).filter fun x => !(x.testBit p || x.testBit q)

/-- The two numbers are the counts of AND and OR restrictions, respectively. -/
def profile (p q : Nat) : Nat × Nat :=
  (count (contexts p q) (cofactor p q) 8, count (contexts p q) (cofactor p q) 14)

theorem exact_error (p q : Nat) :
    let K := contexts p q
    let F := cofactor p q
    (∀ d a b, min (profile p q).1 (profile p q).2 ≤ loss K F d a b) ∧
    ∃ d a b, loss K F d a b = min (profile p q).1 (profile p q).2 :=
  optimum _ _ (mono p q)

def publishedProfiles : List (Nat × Nat × Nat × Nat) :=
  [(0,1,0,16),
   (0,2,0,12),
   (0,3,0,18),
   (0,4,13,11),
   (0,5,16,8),
   (0,6,0,16),
   (0,7,0,24),
   (0,8,0,24),
   (0,9,0,22),
   (1,2,19,5),
   (1,3,0,12),
   (1,4,0,24),
   (1,5,0,18),
   (1,6,13,11),
   (1,7,0,30),
   (1,8,0,30),
   (1,9,0,24),
   (2,3,0,16),
   (2,4,0,24),
   (2,5,0,30),
   (2,6,0,30),
   (2,7,13,11),
   (2,8,0,18),
   (2,9,0,24),
   (3,4,13,11),
   (3,5,0,24),
   (3,6,0,24),
   (3,7,0,16),
   (3,8,16,8),
   (3,9,0,22),
   (4,5,0,36),
   (4,6,0,36),
   (4,7,0,36),
   (4,8,0,36),
   (4,9,9,19),
   (5,6,0,34),
   (5,7,9,19),
   (5,8,9,19),
   (5,9,0,28),
   (6,7,0,30),
   (6,8,9,19),
   (6,9,12,16),
   (7,8,0,34),
   (7,9,12,16),
   (8,9,0,28)]
private theorem row0 : ∀ j : Fin 10, 0 < j.val → (publishedProfiles.contains (0,j.val,(profile 0 j.val).1,(profile 0 j.val).2)) = true := by decide +kernel
private theorem row1 : ∀ j : Fin 10, 1 < j.val → (publishedProfiles.contains (1,j.val,(profile 1 j.val).1,(profile 1 j.val).2)) = true := by decide +kernel
private theorem row2 : ∀ j : Fin 10, 2 < j.val → (publishedProfiles.contains (2,j.val,(profile 2 j.val).1,(profile 2 j.val).2)) = true := by decide +kernel
private theorem row3 : ∀ j : Fin 10, 3 < j.val → (publishedProfiles.contains (3,j.val,(profile 3 j.val).1,(profile 3 j.val).2)) = true := by decide +kernel
private theorem row4 : ∀ j : Fin 10, 4 < j.val → (publishedProfiles.contains (4,j.val,(profile 4 j.val).1,(profile 4 j.val).2)) = true := by decide +kernel
private theorem row5 : ∀ j : Fin 10, 5 < j.val → (publishedProfiles.contains (5,j.val,(profile 5 j.val).1,(profile 5 j.val).2)) = true := by decide +kernel
private theorem row6 : ∀ j : Fin 10, 6 < j.val → (publishedProfiles.contains (6,j.val,(profile 6 j.val).1,(profile 6 j.val).2)) = true := by decide +kernel
private theorem row7 : ∀ j : Fin 10, 7 < j.val → (publishedProfiles.contains (7,j.val,(profile 7 j.val).1,(profile 7 j.val).2)) = true := by decide +kernel
private theorem row8 : ∀ j : Fin 10, 8 < j.val → (publishedProfiles.contains (8,j.val,(profile 8 j.val).1,(profile 8 j.val).2)) = true := by decide +kernel
theorem certified_profiles (p q : Fin 10) (lt : p < q) :
    publishedProfiles.contains (p.val,q.val,(profile p.val q.val).1,(profile p.val q.val).2) = true := by
  fin_cases p <;> first | exact row0 q lt | exact row1 q lt | exact row2 q lt | exact row3 q lt | exact row4 q lt | exact row5 q lt | exact row6 q lt | exact row7 q lt | exact row8 q lt | (change 9 < q.val at lt; omega)

/-- A root whose two operands omit different vertices needs a non-AND-like decoder.
For an edge, even the best possible fixed decoder has at least five errors. -/
theorem constraints (p q : Fin 10) (lt : p < q) :
    5 ≤ (profile p.val q.val).2 ∧
    ((edges.contains (p.val,q.val) = true) ↔ 5 ≤ min (profile p.val q.val).1 (profile p.val q.val).2) ∧
    ((edges.contains (p.val,q.val) = false) → (profile p.val q.val).1 = 0) := by
  have h := certified_profiles p q lt
  have clean : ∀ z ∈ publishedProfiles, 5 ≤ z.2.2.2 ∧
      (edges.contains (z.1,z.2.1) = true ↔ 5 ≤ min z.2.2.1 z.2.2.2) ∧
      (edges.contains (z.1,z.2.1) = false → z.2.2.1 = 0) := by decide +kernel
  exact clean _ (by simpa using h)

end PEqualNP.Research.PuncturedPetersen

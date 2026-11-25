import PEqualNP.Research.L_meta_9822_profiles

namespace PEqualNP.Research.PuncturedPetersen
open PEqualNP.Research.DecoderSlices
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def gate (d : Table) (a b : Bool) : Bool := d.val.testBit (a.toNat + 2*b.toNat)
def enc (x y : Bool) : Encoder := ⟨x.toNat + 2*y.toNat,by cases x <;> cases y <;> decide⟩
def pack (a b c d : Bool) := a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat

theorem pack_pattern : ∀ (d : Table) (a b c e : Bool), pattern d (enc a b) (enc c e) =
    pack (gate d a c) (gate d b c) (gate d a e) (gate d b e) := by decide +kernel
theorem pack_table : ∀ s : Table,
    pack (s.val.testBit 0) (s.val.testBit 1) (s.val.testBit 2) (s.val.testBit 3) = s.val := by decide +kernel

def Omits (h : Nat → Bool) (i : Nat) := ∀ x, h (x ||| 2^i) = h x

theorem slice_witness (d : Table) (u v : Nat → Bool) (p q : Nat) (hu : Omits u q) (hv : Omits v p)
    (comp : ∀ x, gate d (u x) (v x) = target x) (x : Nat) :
    pattern d (enc (u x) (u (x ||| 2^p))) (enc (v x) (v (x ||| 2^q))) = (cofactor p q x).val := by
  obtain ⟨ta,tb,tc,td⟩ := four_entries p q x
  rw [pack_pattern,← pack_table (cofactor p q x),ta,tb,tc,td,← comp,← comp,← comp,← comp]
  have vv : v ((x ||| 2^p) ||| 2^q) = v (x ||| 2^q) := by
    simpa only [Nat.or_assoc,Nat.or_comm,Nat.or_left_comm] using hv (x ||| 2^q)
  rw [hv x,hu x,hu (x ||| 2^p),vv]

def canJoin (d : Table) := ∃ a b : Encoder, pattern d a b = 14
instance (d : Table) : Decidable (canJoin d) := inferInstanceAs (Decidable (∃ _ _, _))

theorem join_tables : ∀ d : Table, canJoin d ↔ d=7 ∨ d=11 ∨ d=13 ∨ d=14 := by decide +kernel
theorem positive_count {keys f t} (h : 0 < count keys f t) : ∃ k ∈ keys, f k = t := by
  induction keys with
  | nil => simp [count] at h
  | cons k ks ih =>
    by_cases e : f k = t
    · exact ⟨k,by simp,e⟩
    · obtain ⟨z,hz,eq⟩ := ih (by simpa [count,e] using h)
      exact ⟨z,by simp [hz],eq⟩

/-- The encoders are arbitrary Boolean functions of the other nine inputs. -/
theorem root_constraint (d : Table) (u v : Nat → Bool) (p q : Fin 10) (lt : p < q)
    (hu : Omits u q.val) (hv : Omits v p.val) (comp : ∀ x, gate d (u x) (v x) = target x) :
    (d=7 ∨ d=11 ∨ d=13 ∨ d=14) ∧ edges.contains (p.val,q.val) = false := by
  obtain ⟨large,forbid,_⟩ := constraints p q lt
  have pos : 0 < (profile p.val q.val).2 := lt_of_lt_of_le (by decide : 0<5) large
  obtain ⟨x,_,hx⟩ := positive_count (keys := contexts p.val q.val) (f := cofactor p.val q.val) (t := 14) pos
  have w := slice_witness d u v p.val q.val hu hv comp
  have hj : canJoin d := ⟨_,_,(w x).trans (by rw [hx]; rfl)⟩
  refine ⟨(join_tables d).mp hj,?_⟩
  cases eq : edges.contains (p.val,q.val) with
  | false => rfl
  | true =>
    have big := forbid.mp eq
    have pos' : 0 < (profile p.val q.val).1 := lt_of_lt_of_le (by decide : 0<5) (big.trans (min_le_left _ _))
    obtain ⟨y,_,hy⟩ := positive_count (keys := contexts p.val q.val) (f := cofactor p.val q.val) (t := 8) pos'
    have hMeet : canMeet d := ⟨_,_,(w y).trans (by rw [hy]; rfl)⟩
    obtain ⟨a,b,ha⟩ := hj
    exact (incompatible d hMeet a b ha).elim

/-- For a nonedge, freezing either private vertex to zero gives explicit local encoders. -/
def clear (x i : Nat) := x &&& (1023 - 2^i)
theorem deletion_decoder : ∀ (p q : Fin 10), p < q → edges.contains (p.val,q.val) = false →
    ∀ x : Fin 1024, (target (clear x.val p.val) || target (clear x.val q.val)) = target x.val := by decide +kernel

end PEqualNP.Research.PuncturedPetersen

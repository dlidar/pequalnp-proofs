import PEqualNP.Research.PuncturedProtocol

namespace PEqualNP.Research.PuncturedPlaneCut
open Finset

def keyOf (x : Side) : Key := ⟨visible 21 [] x,(mem_messages [] (by simp)).mpr ⟨x,rfl⟩⟩
private theorem allOff (n : Nat) : neighborhood (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [neighborhood] using ih
def offKey := keyOf (fun _ => false)
theorem offKey_val : offKey.val = 0 := allOff 21

noncomputable def scan : List Key → Protocol
  | [] => .leaf false
  | a :: tail => .point (fun x => decide (keyOf x = a))
    (.line (fun y => posted (input 21 [] (rowInput a) y)) (.leaf true) (.leaf false)) (scan tail)

theorem scan_leaves (s : List Key) : (scan s).leaves false = s.length+1 ∧
    (scan s).leaves true = s.length := by
  induction s with
  | nil => exact ⟨rfl,rfl⟩
  | cons a s ih =>
    simp [scan,Protocol.leaves,ih.1,ih.2,Nat.add_comm]

theorem scan_value (s : List Key) (x y : Side) : (scan s).eval x y =
    (decide (keyOf x ∈ s) && posted (input 21 [] x y)) := by
  induction s with
  | nil => simp [scan,Protocol.eval]
  | cons a s ih =>
    by_cases h : keyOf x = a
    · have eq := (indistinguishable (by decide : 21≤21) [] (by simp) x (rowInput a)).mpr
        ((congrArg Subtype.val h).trans (row_key a).symm)
      simp [scan,Protocol.eval,h,eq y]
    · simp [scan,Protocol.eval,h,ih]

theorem sharp_leaf_counts : ∃ p : Protocol, p.leaves false = 24925 ∧ p.leaves true = 24924 ∧
    ∀ x y, p.eval x y = posted (input 21 [] x y) := by
  classical
  let s := ((Finset.univ : Finset Key).erase offKey).toList
  have tot : Fintype.card Key = 24925 := (Fintype.card_coe (messages 21 [])).trans full_count
  have len : s.length = 24924 := by
    dsimp only [s]
    rw [Finset.length_toList,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,tot]
  refine ⟨scan s,by rw [(scan_leaves s).1,len],by rw [(scan_leaves s).2,len],?_⟩
  intro x y
  rw [scan_value]
  by_cases off : keyOf x = offKey
  · have zero : neighborhood x 21 = 0 := (congrArg Subtype.val off).trans offKey_val
    have no : posted (input 21 [] x y) = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,_,_,on,_⟩ := (posted_restricted (by decide : 21≤21) [] _ _).mp yes
      simp [zero] at on
    simp [no]
  · have mem : keyOf x ∈ s := Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨off,Finset.mem_univ _⟩)
    simp [mem]

theorem positive_products_attained (K : Type*) [Field K] : Factors K 24924 (oneRow K) := by
  obtain ⟨p,_,hp,correct⟩ := sharp_leaf_counts
  obtain ⟨A,B,good⟩ := p.factors K true
  rw [←hp]
  refine ⟨A,B,?_⟩
  intro x y
  simpa only [oneRow,correct] using good x y

end PEqualNP.Research.PuncturedPlaneCut

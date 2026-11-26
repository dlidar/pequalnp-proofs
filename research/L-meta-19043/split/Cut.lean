import Core
namespace PEqualNP.Outside.Mask5805

theorem unary_mono {a : Sig} {r ws : List Sig} {e t : Nat} {f g : List Sig → Bool}
    (le : ∀ l, f l = true → g l = true) :
    dispatchUnary e t ws f a r = true → dispatchUnary e t ws g a r = true := by
  unfold dispatchUnary
  dsimp only
  split
  · simp
  · simp only [Bool.or_eq_true, Bool.and_eq_true]
    rintro (⟨c,h⟩ | ⟨⟨c,b⟩,h⟩)
    · exact Or.inl ⟨c,le _ h⟩
    · exact Or.inr ⟨⟨c,b⟩,le _ h⟩

theorem bin_mono {a b : Sig} {r ws : List Sig} {e : Nat} {t : Bool} {f g : List Sig → Bool}
    (le : ∀ l, f l = true → g l = true) :
    dispatchBin e t ws f a b r = true → dispatchBin e t ws g a b r = true := by
  unfold dispatchBin
  dsimp only
  simp only [Bool.or_eq_true, Bool.and_eq_true, ite_eq_left_iff, Bool.false_eq_true]
  intro h
  rcases h with h | h
  · left
    split at h <;> rename_i htest
    · contradiction
    · rw [if_neg htest]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      grind
  · right
    split at h <;> rename_i htest
    · contradiction
    · rw [if_neg htest]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      grind

def stepCheck (k t : Nat) (ws : List Sig) (f : Nat → List Sig → Bool) : Bool :=
  ((t == 0) && (ws == [target])) ||
    (if t == 0 then false else
      (singles ws).any (fun (a,r) => dispatchUnary (k + 2 - ws.length - t) (t-1) ws (f (t-1)) a r)) ||
    (pairs ws).any (fun (a,b,r) => dispatchBin (k + 2 - ws.length - t) (t != 0) ws (f t) a b r)

theorem step_mono {k t : Nat} {ws : List Sig} {f g : Nat → List Sig → Bool}
    (le : ∀ n l, f n l = true → g n l = true) :
    stepCheck k t ws f = true → stepCheck k t ws g = true := by
  unfold stepCheck
  simp only [Bool.or_eq_true]
  rintro ((h | h) | h)
  · exact Or.inl (Or.inl h)
  · apply Or.inl ∘ Or.inr
    split at h <;> rename_i ht
    · contradiction
    · rw [if_neg ht]
      obtain ⟨⟨a,r⟩,m,v⟩ := List.any_eq_true.mp h
      exact List.any_eq_true.mpr ⟨(a,r),m,unary_mono (le _) v⟩
  · right
    obtain ⟨⟨a,b,r⟩,m,v⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨(a,b,r),m,bin_mono (le _) v⟩

theorem prune (k t : Nat) (ws : List Sig) (denied : List (Nat × List Sig))
    (children : ∀ p ∈ denied, search k p.1 p.2 = false)
    (hc : stepCheck k t ws (fun n l => (!denied.contains (n,l)) && search k n l) = false) :
    search (k+1) t ws = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  change stepCheck k t ws (search k) = true at h
  have le : ∀ n l, search k n l = true → ((!denied.contains (n,l)) && search k n l) = true := by
    intro n l hh
    simp only [Bool.and_eq_true, hh, and_true]
    by_contra! contrary
    have mem : (n,l) ∈ denied := by simpa using contrary
    have hn := children _ mem
    simp_all
  have := step_mono le h
  simp_all
end PEqualNP.Outside.Mask5805

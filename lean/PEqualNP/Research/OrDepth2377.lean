import PEqualNP.Research.ClausePairs2377

namespace PEqualNP.Research.OrDepth2377
open PEqualNP.Research.ClausePairs2377
open scoped Sym2

/-- Unfolding a shared AND/OR computation into a formula preserves the
number of OR gates on its deepest path and the identities of its inputs. -/
inductive Expr (d : Nat) where
  | atom : Fin d → Expr d
  | meet : Expr d → Expr d → Expr d
  | join : Expr d → Expr d → Expr d

def ev {d : Nat} (v : Fin d → Bool) : Expr d → Bool
  | .atom i => v i
  | .meet a b => ev v a && ev v b
  | .join a b => ev v a || ev v b

def depth {d : Nat} : Expr d → Nat
  | .atom _ => 0
  | .meet a b => max (depth a) (depth b)
  | .join a b => max (depth a) (depth b) + 1

theorem zero_certificate {d : Nat} (v : Fin d → Bool) (e : Expr d) (h : ev v e = false) :
    ∃ s : Finset (Fin d), s.Nonempty ∧ s.card ≤ 2^(depth e) ∧ (∀ i ∈ s, v i = false) ∧
      ∀ w : Fin d → Bool, (∀ i ∈ s, w i = false) → ev w e = false := by
  induction e with
  | atom i => exact ⟨{i},by simp,by simp [depth],by simpa [ev] using h,by simp [ev]⟩
  | meet a b ia ib =>
    have liftA : 2^depth a ≤ 2^depth (.meet a b) := Nat.pow_le_pow_right (by decide) (le_max_left ..)
    have liftB : 2^depth b ≤ 2^depth (.meet a b) := Nat.pow_le_pow_right (by decide) (le_max_right ..)
    rcases Bool.and_eq_false_iff.mp h with ha|hb
    · obtain ⟨s,ne,sz,z,all⟩ := ia ha
      exact ⟨s,ne,sz.trans liftA,z,fun w hw => by simp [ev,all w hw]⟩
    · obtain ⟨s,ne,sz,z,all⟩ := ib hb
      exact ⟨s,ne,sz.trans liftB,z,fun w hw => by simp [ev,all w hw]⟩
  | join a b ia ib =>
    obtain ⟨ha,hb⟩ := Bool.or_eq_false_iff.mp h
    obtain ⟨s,ne,sz,z,all⟩ := ia ha
    obtain ⟨t,_,tz,u,every⟩ := ib hb
    refine ⟨s ∪ t, ne.mono Finset.subset_union_left,?_,?_,?_⟩
    · have A : 2^depth a ≤ 2^(max (depth a) (depth b)) := Nat.pow_le_pow_right (by decide) (le_max_left ..)
      have B : 2^depth b ≤ 2^(max (depth a) (depth b)) := Nat.pow_le_pow_right (by decide) (le_max_right ..)
      have := Finset.card_union_le s t
      simp only [depth,pow_succ]
      omega
    · intro i hi
      exact (Finset.mem_union.mp hi).elim (z i) (u i)
    · intro w hw
      simp [ev,all w (fun i hi => hw i (Finset.mem_union_left _ hi)),
        every w (fun i hi => hw i (Finset.mem_union_right _ hi))]

theorem two_atoms {d : Nat} (e : Expr d) (small : depth e ≤ 1) (v : Fin d → Bool)
    (h : ev v e = false) : ∃ i j, v i = false ∧ v j = false ∧
    ∀ w : Fin d → Bool, w i = false → w j = false → ev w e = false := by
  obtain ⟨s,ne,sz,z,all⟩ := zero_certificate v e h
  have le : s.card ≤ 2 := sz.trans (Nat.pow_le_pow_right (by decide) small : 2^depth e ≤ 2^1)
  obtain ⟨i,hi⟩ := ne
  by_cases single : s = {i}
  · exact ⟨i,i,z i hi,z i hi,fun w hw _ => all w (by simpa [single] using hw)⟩
  · have ex : ∃ j ∈ s, j ≠ i := by
      by_contra! h
      exact single (Finset.ext (fun x => by simpa using Iff.intro (h x) (fun eq => eq ▸ hi)))
    obtain ⟨j,hj,ne⟩ := ex
    have sub : ({i,j} : Finset _) ⊆ s := by intro k hk; simp only [Finset.mem_insert,Finset.mem_singleton] at hk; rcases hk with rfl|rfl <;> assumption
    have eq := Finset.eq_of_subset_of_card_le sub (show s.card ≤ ({i,j} : Finset _).card by simpa [Ne.symm ne] using le)
    exact ⟨i,j,z i hi,z j hj,fun w wi wj => all w (by rw [← eq]; simp [wi,wj])⟩

theorem shallow_separated {d : Nat} (L R : Fin d → Key → Bool) (e : Expr d)
    (rep : ∀ m n, ev (fun i => L i m || R i n) e = cross m n) (small : depth e ≤ 1) :
    225 ≤ d := by
  classical
  let cert (i j : Fin d) := ∀ w : Fin d → Bool, w i = false → w j = false → ev w e = false
  let used : Set (Sym2 (Fin d)) := {p | ∃ i j, p = s(i,j) ∧ cert i j}
  apply pair_dictionary L R used
  intro m n
  rw [← rep]
  constructor
  · intro no
    obtain ⟨i,j,vi,vj,h⟩ := two_atoms e small _ no
    refine ⟨s(i,j),⟨i,j,rfl,h⟩,?_⟩
    intro k hk
    rcases Sym2.mem_iff.mp hk with eq|eq
    · subst k; exact Bool.or_eq_false_iff.mp vi
    · subst k; exact Bool.or_eq_false_iff.mp vj
  · rintro ⟨_,⟨i,j,rfl,h⟩,both⟩
    exact h _ (Bool.or_eq_false_iff.mpr (both i (Sym2.mem_mk_left i j)))
      (Bool.or_eq_false_iff.mpr (both j (Sym2.mem_mk_right i j)))

theorem two_or_gates_on_a_path {s : Nat} (h : s ≤ 103)
    (L R : Fin (42+s) → Key → Bool) (e : Expr (42+s))
    (rep : ∀ m n, ev (fun i => L i m || R i n) e = cross m n) : 2 ≤ depth e := by
  by_contra! H
  have := shallow_separated L R e rep (by omega)
  omega
end PEqualNP.Research.OrDepth2377

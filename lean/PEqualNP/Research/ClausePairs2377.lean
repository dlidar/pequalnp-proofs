import Mathlib
import PEqualNP.Research.L_meta_9761_plane_cut

namespace PEqualNP.Research.ClausePairs2377
open PEqualNP.Research.PlaneCut
open scoped Sym2
abbrev Key := ↥(messages 21 [])
noncomputable def points (m : Key) := representative (by simp) m
def lines (m : Key) (l : Nat) := !m.val.testBit l
noncomputable def cross (m n : Key) := posted (input 21 [] (points m) (lines n))

theorem row_bits (m : Key) : neighborhood (points m) 21 = m.val := by
  simpa [visible,points] using representative_eq (by simp : ∀ j ∈ ([] : List Nat), j < 21) m

theorem cross_iff (m n : Key) : cross m n = true ↔
    ∃ l < 21, m.val.testBit l = true ∧ n.val.testBit l = false := by
  simp [cross, posted_restricted (by decide : 21 ≤ 21), row_bits, lines]

theorem diagonal (m : Key) : cross m m = false := by
  cases h : cross m m with
  | false => rfl
  | true =>
    obtain ⟨l,_,on,off⟩ := (cross_iff m m).mp h
    simp_all

theorem ordered {m n : Key} (hf : cross m n = false) (hb : cross n m = false) : m = n := by
  apply Subtype.ext
  apply Nat.eq_of_testBit_eq
  intro l
  by_cases lt : l < 21
  · cases a : m.val.testBit l <;> cases b : n.val.testBit l <;> try rfl
    · have := (cross_iff n m).mpr ⟨l,lt,b,a⟩
      simp_all
    · have := (cross_iff m n).mpr ⟨l,lt,a,b⟩
      simp_all
  · have bound (k : Key) : k.val < 2^l := by
      rw [← row_bits k]
      exact (neighborhood_bound _ _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (bound m),Nat.testBit_lt_two_pow (bound n)]

theorem rectangle_labels {D : Type*} [Fintype D] (label : Key → D)
    (crossing : ∀ m n, label m = label n → cross m n = false) : 25237 ≤ Fintype.card D := by
  have inj : Function.Injective label := fun m n h => ordered (crossing m n h) (crossing n m h.symm)
  simpa [Fintype.card_coe,full_count] using Fintype.card_le_of_injective label inj

theorem pair_dictionary {d : Nat} (L R : Fin d → Key → Bool) (used : Set (Sym2 (Fin d)))
    (accept : ∀ m n, cross m n = false ↔
      ∃ p ∈ used, ∀ i ∈ p, L i m = false ∧ R i n = false) : 225 ≤ d := by
  classical
  have ex (m : Key) := (accept m m).mp (diagonal m)
  let label : Key → Sym2 (Fin d) := fun m => Classical.choose (ex m)
  have h := rectangle_labels label (by
    intro m n eq
    apply (accept m n).mpr
    obtain ⟨hm,am⟩ := Classical.choose_spec (ex m)
    obtain ⟨_,an⟩ := Classical.choose_spec (ex n)
    refine ⟨label m,hm,?_⟩
    intro i hi
    exact ⟨(am i hi).1,(an i (show i ∈ label n from eq ▸ hi)).2⟩)
  rw [Sym2.card,Fintype.card_fin] at h
  by_contra! bad
  have le : d + 1 ≤ 225 := by omega
  have up := Nat.choose_le_choose 2 le
  have num : Nat.choose 225 2 = 25200 := by norm_num [Nat.choose_two_right]
  omega

/-- Each rule ORs two conjunctions of shared predicates, and the decoder ANDs all rules. -/
theorem rule_dictionary {d : Nat} (L R : Fin d → Key → Bool)
    (rules : List (List (Fin d) × List (Fin d)))
    (rep : ∀ m n, cross m n = rules.all (fun r =>
      (r.1.all (fun i => L i m || R i n)) || (r.2.all (fun i => L i m || R i n)))) :
    225 ≤ d := by
  let used : Set (Sym2 (Fin d)) := {p | ∃ r ∈ rules, ∃ i ∈ r.1, ∃ j ∈ r.2, p = s(i,j)}
  apply pair_dictionary L R used
  intro m n
  rw [rep]
  constructor
  · intro bad
    obtain ⟨r,hr,b⟩ := List.all_eq_false.mp bad
    have b := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr b)
    obtain ⟨i,hi,bi⟩ := List.all_eq_false.mp b.1
    obtain ⟨j,hj,bj⟩ := List.all_eq_false.mp b.2
    refine ⟨s(i,j),⟨r,hr,i,hi,j,hj,rfl⟩,?_⟩
    intro k hk
    rcases Sym2.mem_iff.mp hk with h|h
    · subst k; exact Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bi)
    · subst k; exact Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bj)
  · rintro ⟨p,⟨r,hr,i,hi,j,hj,rfl⟩,hp⟩
    apply List.all_eq_false.mpr
    refine ⟨r,hr,?_⟩
    have bi := hp i (Sym2.mem_mk_left i j)
    have bj := hp j (Sym2.mem_mk_right i j)
    apply Bool.eq_false_iff.mp
    apply Bool.or_eq_false_iff.mpr
    exact ⟨List.all_eq_false.mpr ⟨i,hi,Bool.eq_false_iff.mp (Bool.or_eq_false_iff.mpr bi)⟩,
      List.all_eq_false.mpr ⟨j,hj,Bool.eq_false_iff.mp (Bool.or_eq_false_iff.mpr bj)⟩⟩

theorem learned_entries {s : Nat} (L R : Fin (42 + s) → Key → Bool)
    (rules : List (List (Fin (42+s)) × List (Fin (42+s))))
    (rep : ∀ m n, cross m n = rules.all (fun r =>
      (r.1.all (fun i => L i m || R i n)) || (r.2.all (fun i => L i m || R i n)))) :
    183 ≤ s := by have := rule_dictionary L R rules rep; omega

end PEqualNP.Research.ClausePairs2377

import Hash
namespace SpinHash
open Finset SpinMass
variable {t b k : ℕ}
def ordered {n : ℕ} (a b : Fin n) : Option (Pair n) :=
  if h : a < b then some ⟨(a,b),h⟩ else
  if h : b < a then some ⟨(b,a),h⟩ else none

theorem ordered_swap {n : ℕ} (a b : Fin n) : ordered a b = ordered b a := by
  unfold ordered
  rcases lt_trichotomy a b with h|h|h <;> simp_all [not_lt_of_ge] <;> omega

theorem ordered_some {n : ℕ} (a b : Fin n) (e : Pair n) :
    ordered a b = some e ↔ (a = e.val.1 ∧ b = e.val.2) ∨ (a = e.val.2 ∧ b = e.val.1) := by
  have he := e.property
  rcases e with ⟨⟨i,j⟩,he'⟩
  change i < j at he
  unfold ordered
  split_ifs with h h' <;> simp only [Option.some.injEq,Subtype.mk.injEq,Prod.mk.injEq,reduceCtorEq]
  all_goals constructor <;> rintro h₀ <;> first | tauto | rcases h₀ with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp_all | omega
  all_goals omega

def project (c : Label t b) (g : Option (Pair t)) : Option (Pair b) :=
  g.bind (fun u => ordered (c u.val.1) (c u.val.2))

def safe (c : Label t b) (a : Fin t × Fin t) := c a.1 = c a.2 → a.1 = a.2

def guards (e : Pair t) (u : Option (Pair t)) : List (Fin t × Fin t) :=
  u.elim [] (fun f => [f.val,(e.val.1,f.val.1),(e.val.1,f.val.2),(e.val.2,f.val.1),(e.val.2,f.val.2)])

def critical (e : Pair t) (G : Model t k) : List (Fin t × Fin t) :=
  e.val :: (List.ofFn fun l => guards e (G l)).flatten

theorem critical_size (e : Pair t) (G : Model t k) : (critical e G).length ≤ 5*k+1 := by
  have hi (l : Fin k) : (guards e (G l)).length ≤ 5 := by cases G l <;> simp [guards]
  simp only [critical,List.length_cons,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  have hh := Finset.sum_le_sum (s := univ) (fun l _ => hi l)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  change (∑ l, (guards e (G l)).length) ≤ k*5 at hh
  simpa [Nat.mul_comm] using Nat.add_le_add_right hh 1

theorem guard_mem (e : Pair t) (G : Model t k) (l : Fin k) {p : Fin t × Fin t}
    (hp : p ∈ guards e (G l)) : p ∈ critical e G := by
  apply List.mem_cons_of_mem
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨l,rfl⟩,hp⟩

theorem ordered_eq {n : ℕ} {a b c d : Fin n} (h : a ≠ b) :
    ordered a b = ordered c d ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  cases h' : ordered a b with
  | none =>
    unfold ordered at h'
    split_ifs at h' <;> simp_all <;> omega
  | some e =>
    have hab := (ordered_some a b e).mp h'
    rw [eq_comm, ordered_some]
    rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> grind

theorem project_preserves {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) :
    ∃ q : Pair b, project c (some e) = some q ∧ mult (fun l => project c (G l)) q = mult G e := by
  have he := hc e.val (by simp [critical])
  have hne : c e.val.1 ≠ c e.val.2 := fun hh => (ne_of_lt e.property) (he hh)
  have hsome : (ordered (c e.val.1) (c e.val.2)).isSome := by
    unfold ordered; split_ifs <;> simp_all <;> omega
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨q,hq,?_⟩
  unfold mult
  congr 1
  apply filter_congr
  intro l _
  cases hu : G l with
  | none => simp [hu,project]
  | some u =>
    have hv (p) (hp : p ∈ guards e (some u)) : safe c p :=
      hc p (guard_mem e G l (hu ▸ hp))
    have h₁ := hv (e.val.1,u.val.1) (by simp [guards])
    have h₂ := hv (e.val.2,u.val.2) (by simp [guards])
    have h₃ := hv (e.val.1,u.val.2) (by simp [guards])
    have h₄ := hv (e.val.2,u.val.1) (by simp [guards])
    simp only [hu,project,Option.bind_some,Option.some.injEq]
    rw [← hq,eq_comm,ordered_eq hne]
    constructor
    · rintro (⟨ha,hb⟩|⟨ha,hb⟩)
      · exact Subtype.ext (Prod.ext (h₁ ha).symm (h₂ hb).symm)
      · have h₅ := h₃ ha; have h₆ := h₄ hb
        change e.val.1 = u.val.2 at h₅; change e.val.2 = u.val.1 at h₆
        have he' := e.property;have hu' := u.property;omega
    · rintro rfl; exact Or.inl ⟨rfl,rfl⟩

theorem tag_project {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (l : Fin k) (m : Mask b) :
    tag (project c (G l)) m = tag (G l) (m ∘ c) := by
  cases hu : G l with
  | none => rfl
  | some u =>
    have hs := hc u.val (guard_mem e G l (hu ▸ (by simp [guards] : u.val ∈ guards e (some u))))
    have hn : c u.val.1 ≠ c u.val.2 := fun hh => (ne_of_lt u.property) (hs hh)
    have symm_factor : ∀ x y, factor x y = factor y x := by decide
    change tag (ordered (c u.val.1) (c u.val.2)) m = _
    unfold ordered; split_ifs with h h'
    · rfl
    · exact symm_factor _ _
    · omega
end SpinHash

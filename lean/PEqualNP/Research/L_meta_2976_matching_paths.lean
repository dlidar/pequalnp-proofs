import PEqualNP.Research.L_meta_4960_small_cover

namespace PEqualNP.Research.MatchingPaths
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem support (N : ℕ) (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N)) (C : Circuit)
    (matching : ∀ i, (i,p i) ∈ E) (strict : IsAO2 (N+N) C)
    (eval : ∀ x, circuitFun (N+N) C x = decide (∃ a b, (a,b) ∈ E ∧
      x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) : 2*N ≤ C.size+1 := by
  have h := SmallCover.endpoint_bound N N E C (fun g hg => (strict.2.2 g hg).le) eval
  have rows : E.image Prod.fst = univ := eq_univ_of_forall fun i => mem_image.mpr ⟨_,matching i,rfl⟩
  have cols : E.image Prod.snd = univ := eq_univ_of_forall fun i =>
    mem_image.mpr ⟨_,matching (p.symm i), p.apply_symm_apply i⟩
  simpa [rows,cols,two_mul] using h

variable {N : ℕ} (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N))
def arc (i j : Fin N) := i ≠ j ∧ (i,p j) ∈ E
def Thin := ∀ a c b d : Fin N, a ≠ c → b ≠ d →
  ¬ ((a,b) ∈ E ∧ (a,d) ∈ E ∧ (c,b) ∈ E ∧ (c,d) ∈ E)

theorem no_reverse (thin : Thin E) (matching : ∀ i, (i,p i) ∈ E)
    {i j} (h : arc E p i j) : (j,p i) ∉ E := fun rev =>
  thin i j (p i) (p j) h.1 (p.injective.ne h.1) ⟨matching i,h.2,rev,matching j⟩

theorem no_shortcut (thin : Thin E) (matching : ∀ i, (i,p i) ∈ E)
    {i j k} (a : arc E p i j) (b : arc E p j k) : (i,p k) ∉ E := fun short =>
  thin i j (p j) (p k) a.1 (p.injective.ne b.1) ⟨a.2,short,matching j,b.2⟩

/-- Distinct starting vertices cannot share two out-neighbors, even when the matching edges count. -/
theorem common_successor (thin : Thin E) {i j k l : Fin N} (ij : i ≠ j)
    (ik : (i,p k) ∈ E) (il : (i,p l) ∈ E) (jk : (j,p k) ∈ E) (jl : (j,p l) ∈ E) : k = l := by
  by_contra ne
  exact thin i j (p k) (p l) ij (p.injective.ne ne) ⟨ik,il,jk,jl⟩

def extras := E.filter fun e => e.2 ≠ p e.1
theorem surplus_count (matching : ∀ i, (i,p i) ∈ E) : (extras E p).card + N = E.card := by
  let M := univ.image fun i : Fin N => (i,p i)
  have ms : M ⊆ E := by intro e he; obtain ⟨i,_,rfl⟩ := mem_image.mp he; exact matching i
  have eq : extras E p = E \ M := by
    ext e; rcases e with ⟨i,j⟩
    simp [extras,M,eq_comm]
  have size : M.card = N := by
    have inj : Function.Injective (fun i : Fin N => (i,p i)) := fun _ _ h => congrArg Prod.fst h
    simp [M,card_image_of_injective _ inj]
  simpa only [eq,size] using card_sdiff_add_card_eq_card ms

/-- On the four inputs supported on two matched pairs, the surplus edge gives exactly a three-edge path. -/
theorem induced_path (thin : Thin E) (matching : ∀ i, (i,p i) ∈ E)
    {i j} (h : arc E p i j) (A B : Finset (Fin N))
    (points : A ⊆ {i,j}) (lines : B ⊆ {p i,p j}) :
    (∃ a ∈ A, ∃ b ∈ B, (a,b) ∈ E) ↔
      (i ∈ A ∧ p i ∈ B) ∨ (i ∈ A ∧ p j ∈ B) ∨ (j ∈ A ∧ p j ∈ B) := by
  constructor
  · rintro ⟨a,ha,b,hb,e⟩
    have pa := points ha
    have pb := lines hb
    simp only [mem_insert,mem_singleton] at pa pb
    rcases pa with rfl|rfl <;> rcases pb with rfl|h' <;> subst_vars <;>
      first | exact Or.inl ⟨ha,hb⟩ | exact Or.inr (Or.inl ⟨ha,hb⟩) |
        exact Or.inr (Or.inr ⟨ha,hb⟩) | exact (no_reverse E p thin matching h e).elim
  · rintro (⟨a,b⟩|⟨a,b⟩|⟨a,b⟩)
    · exact ⟨_,a,_,b,matching i⟩
    · exact ⟨_,a,_,b,h.2⟩
    · exact ⟨_,a,_,b,matching j⟩

/-- Each surplus incidence is exactly one unit of size beyond the essential-input bound. -/
theorem deficit (matching : ∀ i, (i,p i) ∈ E) (C : Circuit)
    (strict : IsAO2 (N+N) C) (eval : ∀ x, circuitFun (N+N) C x = decide
    (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) :
    E.card + N ≤ C.size + 1 ↔ (extras E p).card ≤ C.size + 1 - 2*N := by
  have := support N E p C matching strict eval
  have := surplus_count E p matching
  omega

def linked (i j : Fin N) := arc E p i j ∨ arc E p j i
/-- Any three pairwise linked matching edges form a directed cycle. -/
theorem cycle_of_triangle (thin : Thin E) (matching : ∀ i, (i,p i) ∈ E) {i j k}
    (ij : arc E p i j) (jk : linked E p j k) (ki : linked E p k i) :
    arc E p j k ∧ arc E p k i := by
  rcases jk with jk|kj <;> rcases ki with ki|ik
  · exact ⟨jk,ki⟩
  · exact (no_shortcut E p thin matching ij jk ik.2).elim
  · exact (no_shortcut E p thin matching ki ij kj.2).elim
  · exact (no_shortcut E p thin matching ik kj ij.2).elim

/-- Contracting a perfect matching and forgetting directions cannot produce a four-clique. -/
theorem no_four_clique (thin : Thin E) (matching : ∀ i, (i,p i) ∈ E) {i j k l}
    (ij : linked E p i j) (ik : linked E p i k) (il : linked E p i l)
    (jk : linked E p j k) (jl : linked E p j l) : ¬linked E p k l := by
  intro kl
  have flip {a b} : linked E p a b → linked E p b a := Or.symm
  have exclude {a b c d} (ab : arc E p a b) (ac : linked E p a c) (ad : linked E p a d)
      (bc : linked E p b c) (bd : linked E p b d) (cd : linked E p c d) : False := by
    have t := cycle_of_triangle E p thin matching ab bc (flip ac)
    have s := cycle_of_triangle E p thin matching ab bd (flip ad)
    have u := cycle_of_triangle E p thin matching t.1 cd (flip bd)
    exact no_reverse E p thin matching s.1 u.2.2
  exact ij.elim (fun h => exclude h ik il jk jl kl) (fun h => exclude h jk jl ik il kl)

end PEqualNP.Research.MatchingPaths

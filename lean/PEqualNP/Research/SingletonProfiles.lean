import PEqualNP.Research.NecessarySamples

namespace PEqualNP.Research.SingletonProfiles
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.StarFormulas PEqualNP.Research.FormulaTrace
open PEqualNP.Research.NecessarySamples PEqualNP.Research.StarDesign

def shortcut (dual : Bool) (a : V) : Form :=
  disjunction ((Formula.atom (first dual a)) :: (((List.finRange 13).filter (fun i => decide (i≠a))).map fun i =>
    Formula.meet (Formula.atom (first dual i)) (disjunction (((List.finRange 13).filter
      (fun j => adj dual i j)).map fun j => Formula.atom (second dual j)))))

theorem shortcut_cost : ∀ dual a,gates (shortcut dual a)=60 := by decide +kernel

theorem shortcut_spec (dual a) (x : Input → Bool) :
    truth x (shortcut dual a)=true ↔ x (first dual a)=true ∨ edge dual x := by
  simp [shortcut,truth_or,truth,edge,List.mem_finRange]
  constructor
  · rintro (one|⟨i,_,xi,j,adj,xj⟩)
    · exact Or.inl one
    · exact Or.inr ⟨i,xi,j,xj,adj⟩
  · rintro (one|⟨i,xi,j,xj,adj⟩)
    · exact Or.inl one
    · by_cases eq : i=a
      · exact Or.inl (eq ▸ xi)
      · exact Or.inr ⟨i,eq,xi,j,adj,xj⟩

theorem needs_vertices {α} (data : α → Word) (labels : Set α) (h : hard data labels)
    (yes : ∀ k∈labels,target (data k)) (no : ∀ k∉labels,Generic (data k)) (a : V) :
    (∃ k∉labels,a∈pts (data k)) ∧ (∃ k∉labels,a∈lines (data k)) := by
  have find (d : Bool) : ∃ k∉labels,bits (data k) (first d a)=true := by
    classical
    by_contra! all
    apply excludes h (shortcut d a) (by rw [shortcut_cost];decide)
    intro k
    rw [shortcut_spec]
    have sem : edge d (bits (data k)) ↔ target (data k) := by
      cases d <;> simp [edge_dual,edge_primal,target]
    rw [sem]
    by_cases hk : k∈labels
    · exact ⟨fun _ => Or.inr (yes k hk),fun _ => hk⟩
    · exact ⟨fun k => False.elim (hk k),fun bad => False.elim (bad.elim (by simpa using all k hk) (generic_no_edge (no k hk)))⟩
  exact ⟨by simpa [first,bits_point] using find false,by simpa [first,bits_line] using find true⟩

abbrev SixCode := Finset (Fin 6)
def singles (C : V → SixCode) := (univ.filter fun i => (C i).card=1).card
def weight (C : V → SixCode) := ∑ i,(C i).card

theorem single_limit (C : V → SixCode) (inj : Function.Injective C) : singles C ≤ 6 := by
  let T := univ.filter fun i => (C i).card=1
  have sub : T.image C ⊆ univ.filter (fun S : SixCode => S.card=1) := by
    rintro _ hv;obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  have n : (univ.filter (fun S : SixCode => S.card=1)).card=6 := by decide +kernel
  have b := card_le_card sub
  rwa [n,card_image_of_injective _ inj] at b

theorem single_weight (C : V → SixCode) (nz : ∀ i,(C i).Nonempty) :
    26 ≤ weight C + singles C := by
  have p (i : V) : 2 ≤ (C i).card+(if (C i).card=1 then 1 else 0) := by
    have := card_pos.mpr (nz i);split <;> omega
  have b := sum_le_sum (s:=univ) (fun i _ => p i)
  simp only [sum_add_distrib,sum_boole] at b
  norm_cast at b

def profile (test : Fin 6 → Finset V) (v : V) : SixCode := univ.filter fun j => v∈test j

theorem transpose (test : Fin 6 → Finset V) : weight (profile test) = ∑ i,(test i).card := by
  simp only [weight,profile,card_filter];rw [sum_comm];simp

set_option maxHeartbeats 1800000 in
theorem six_constraints (P L : Fin 6 → Finset V) (pi : Function.Injective (profile P))
    (li : Function.Injective (profile L)) (pc : ∀ v,(profile P v).Nonempty)
    (lc : ∀ v,(profile L v).Nonempty) (cap : ∀ i,(P i).card+(L i).card≤7) :
    20 ≤ weight (profile P) ∧ 20 ≤ weight (profile L) ∧
    10 ≤ singles (profile P)+singles (profile L) ∧
    4 ≤ (univ.filter (fun i => (P i).card+(L i).card=7)).card := by
  have a := single_limit _ pi
  have b := single_limit _ li
  have c := single_weight _ pc
  have d := single_weight _ lc
  have bound := sum_le_sum (s:=univ) (fun i _ => cap i)
  have n : ∑ _ : Fin 6, (7:ℕ)=42 := by decide
  rw [sum_add_distrib,←transpose P,←transpose L,n] at bound
  refine ⟨by omega,by omega,by omega,?_⟩
  have gap (i : Fin 6) : (P i).card+(L i).card ≤ 6+(if (P i).card+(L i).card=7 then 1 else 0) := by
    have := cap i;split <;> omega
  have lim := sum_le_sum (s:=univ) (fun i _ => gap i)
  simp only [sum_add_distrib,sum_boole] at lim
  norm_cast at lim
  have n6 : ∑ _ : Fin 6,(6:ℕ)=36 := by decide
  rw [←transpose P,←transpose L,n6] at lim
  omega

end PEqualNP.Research.SingletonProfiles

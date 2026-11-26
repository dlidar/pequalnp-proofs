import PEqualNP.Research.ExactForest3321
import PEqualNP.MetaComplexity.L106
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.Research.CycleNormal3321
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ForestNormal3321

def next {N : ℕ} (k : Fin (N+N)) : Fin (N+N) :=
  if h : k.val+1 < N+N then ⟨k.val+1,h⟩ else ⟨0,by have := k.isLt;omega⟩
def half {N : ℕ} (k : Fin (N+N)) : Fin N := ⟨k.val / 2,by have := k.isLt;omega⟩
def edge {N : ℕ} (k : Fin (N+N)) : Fin N × Fin N :=
  if k.val % 2 = 0 then (half k,half (next k)) else (half (next k),half k)
def edges (N : ℕ) := (univ : Finset (Fin (N+N))).image edge
def zig {N : ℕ} (k : Fin (N+N)) : Fin (N+N) :=
  if h : k.val < N then ⟨2*k.val,by omega⟩ else ⟨2*(k.val-N)+1,by have := k.isLt;omega⟩

theorem next_index {N : ℕ} (k : Fin (N+N)) : (next k).val = (k.val+1) % (N+N) := by
  unfold next
  split
  · rename_i h; simp [Nat.mod_eq_of_lt h]
  · rename_i h; have eq : k.val+1=N+N := by have := k.isLt;omega
    simp [eq]

theorem edge_labels {N : ℕ} (k : Fin (N+N)) :
    let p := zig (Fin.castAdd N (edge k).1)
    let l := zig (Fin.natAdd N (edge k).2)
    (p = k ∧ l = next k) ∨ (p = next k ∧ l = k) := by
  have low := k.isLt
  have nhi := (next k).isLt
  have ix : (next k).val = if k.val+1 < N+N then k.val+1 else 0 := by unfold next;split <;> simp_all
  have lp (i : Fin N) : (zig (Fin.castAdd N i)).val = 2*i.val := by simp [zig, i.isLt]
  have ll (i : Fin N) : (zig (Fin.natAdd N i)).val = 2*i.val+1 := by simp [zig]
  dsimp only
  by_cases even : k.val%2=0
  · left; constructor <;> apply Fin.ext
    · rw [lp]; simp only [edge,ite_eq_left even,half];omega
    · rw [ll]; simp only [edge,ite_eq_left even,half];split at ix <;> omega
  · right; constructor <;> apply Fin.ext
    · rw [lp]; simp only [edge,ite_eq_right even,half];split at ix <;> omega
    · rw [ll]; simp only [edge,ite_eq_right even,half];omega

theorem cyclic_target {N : ℕ} (x : Fin (N+N) → Bool) :
    Target (edges N) (x ∘ zig) ↔ ∃ i j : Fin (N+N), (i.val+1)%(N+N)=j.val ∧ x i=true ∧ x j=true := by
  constructor
  · rintro ⟨p,l,mem,a,b⟩
    obtain ⟨k,_,eq⟩ := mem_image.mp mem
    have h := edge_labels k
    rw [eq] at h
    change x (zig (Fin.castAdd N p)) = true at a
    change x (zig (Fin.natAdd N l)) = true at b
    refine ⟨k,next k,(next_index k).symm,?_⟩
    rcases h with ⟨u,v⟩|⟨u,v⟩
    · exact ⟨u ▸ a,v ▸ b⟩
    · exact ⟨v ▸ b,u ▸ a⟩
  · rintro ⟨i,j,eq,a,b⟩
    have je : next i = j := Fin.ext ((next_index i).trans eq)
    subst j
    refine ⟨(edge i).1,(edge i).2,mem_image.mpr ⟨i,mem_univ _,rfl⟩,?_⟩
    rcases edge_labels i with ⟨u,v⟩|⟨u,v⟩
    · exact ⟨(congrArg x u).trans a,(congrArg x v).trans b⟩
    · exact ⟨(congrArg x u).trans b,(congrArg x v).trans a⟩

theorem cycle_lower (N : ℕ) (hn : 3 ≤ N) (C : Circuit) (fan : FanInTwo C)
    (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target (edges N) z) : 3*N ≤ C.size+1 := by
  classical
  have h : HasCircuitSize (N+N) (circuitFun (N+N) C) C.size := ⟨C,fan,le_rfl,fun _ => rfl⟩
  have perm := Helpers.PermInputs.relabel_size zig _ _ h
  have eq : (fun x => circuitFun (N+N) C (x ∘ zig)) =
      (fun x => decide (∃ i j : Fin (N+N), (i.val+1)%(N+N)=j.val ∧ x i=true ∧ x j=true)) := by
    funext x; apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (ev _).trans (cyclic_target x)
  rw [eq] at perm
  have bound := (L106 (N+N) C.size (by omega)).mp perm
  omega

theorem cycle_normal (N : ℕ) (hn : 3 ≤ N) (C : Circuit) (fan : FanInTwo C)
    (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target (edges N) z) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (N+N) D z = true ↔ Target (edges N) z) ∧ Below (edges N) D := by
  obtain ⟨D,ao,sz,eval,ok⟩ := compile_cover (edges N) univ ∅ (by simp)
  have he : (edges N).card ≤ N+N := by simpa [edges] using card_image_le (s := (univ : Finset (Fin (N+N)))) (f := edge)
  have lo := cycle_lower N hn C fan ev
  simp only [card_univ,Fintype.card_fin,card_empty,Nat.add_zero] at sz
  exact ⟨D,ao,by omega,eval,ok⟩

end PEqualNP.Research.CycleNormal3321

import PEqualNP.Research.ForestNormal3321
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace PEqualNP.Research.Girth3321
open Finset PEqualNP.Research.ForestCase6390

variable {p l : ℕ} (E : Finset (Fin p × Fin l))
abbrev leftV (i : Fin p) : Fin (p+l) := Fin.castAdd l i
abbrev rightV (j : Fin l) : Fin (p+l) := Fin.natAdd p j

theorem adjacent (u v : Fin (p+l)) : (graph E).Adj u v ↔ ∃ e ∈ E,
    (u = leftV e.1 ∧ v = rightV e.2) ∨ (u = rightV e.2 ∧ v = leftV e.1) := by
  change s(u,v) ∈ (graph E).edgeSet ↔ _
  rw [graph_edges]
  constructor
  · intro h
    obtain ⟨e,he,eq⟩ := mem_map.mp h
    rcases Sym2.eq_iff.mp eq with h|h
    · exact ⟨e,he,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨e,he,Or.inr ⟨h.2.symm,h.1.symm⟩⟩
  · rintro ⟨e,he,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact mem_map.mpr ⟨e,he,rfl⟩
    · exact mem_map.mpr ⟨e,he,Sym2.eq_swap⟩

theorem parity (v : Fin (p+l)) (w : (graph E).Walk v v) : Even w.length := by
  let color : (graph E).Coloring Bool := SimpleGraph.Coloring.mk (fun i => decide (i.val<p)) (by
    intro a b h
    obtain ⟨e,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adjacent E a b).mp h
    all_goals simp [leftV,rightV,e.1.isLt])
  exact (color.even_length_iff_congr w).mpr Iff.rfl

theorem left_right (i : Fin p) (j : Fin l) : (graph E).Adj (leftV i) (rightV j) ↔ (i,j) ∈ E := by
  rw [adjacent]
  constructor
  · rintro ⟨⟨a,b⟩,h,⟨e,f⟩|⟨e,_⟩⟩
    · have hi : i=a := Fin.ext (congrArg (fun t : Fin (p+l) => t.val) e)
      have hj : j=b := by apply Fin.ext; have := congrArg Fin.val f; change p+j.val=p+b.val at this;omega
      simpa [hi,hj] using h
    · exact (different _ _ e).elim
  · exact fun h => ⟨(i,j),h,Or.inl ⟨rfl,rfl⟩⟩

theorem left_left (i k : Fin p) : ¬ (graph E).Adj (leftV i) (leftV k) := by
  rintro h
  obtain ⟨e,_,⟨_,bad⟩|⟨bad,_⟩⟩ := (adjacent E _ _).mp h <;> exact different _ _ bad
theorem right_right (i k : Fin l) : ¬ (graph E).Adj (rightV i) (rightV k) := by
  rintro h
  obtain ⟨e,_,⟨bad,_⟩|⟨_,bad⟩⟩ := (adjacent E _ _).mp h <;> exact different _ _ bad.symm

def SquareFree := ∀ (a b : Fin p) (c d : Fin l), a ≠ b → c ≠ d →
  ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)

theorem no_square (h : SquareFree E) (u v w t : Fin (p+l)) (uv : u ≠ v) (wt : w ≠ t) :
    ¬ ((graph E).Adj u w ∧ (graph E).Adj u t ∧ (graph E).Adj v w ∧ (graph E).Adj v t) := by
  intro four
  obtain ⟨uw,ut,vw,vt⟩ := four
  induction u using Fin.addCases <;> induction w using Fin.addCases <;>
    induction v using Fin.addCases <;> induction t using Fin.addCases
  all_goals first
    | exact left_left E _ _ uw | exact right_right E _ _ uw
    | exact left_left E _ _ ut | exact right_right E _ _ ut
    | exact left_left E _ _ vw | exact right_right E _ _ vw
    | exact left_left E _ _ vt | exact right_right E _ _ vt
    | exact h _ _ _ _ (fun e => uv (congrArg _ e)) (fun e => wt (congrArg _ e))
        ⟨(left_right E _ _).mp uw,(left_right E _ _).mp ut,(left_right E _ _).mp vw,(left_right E _ _).mp vt⟩
    | exact h _ _ _ _ (fun e => wt (congrArg _ e)) (fun e => uv (congrArg _ e))
        ⟨(left_right E _ _).mp uw.symm,(left_right E _ _).mp vw.symm,(left_right E _ _).mp ut.symm,(left_right E _ _).mp vt.symm⟩

theorem six_or_more (h : SquareFree E) (v : Fin (p+l)) (w : (graph E).Walk v v) (hc : w.IsCycle) : 6 ≤ w.length := by
  have low := hc.three_le_length
  obtain ⟨k,hk⟩ := parity E v w
  by_contra! short
  have len : w.length = 4 := by omega
  have nz (a b : Nat) (ha : a<4) (hb : b<4) (hne : a ≠ b) : w.getVert a ≠ w.getVert b :=
    fun e => hne (hc.getVert_injOn' (by change a ≤ w.length-1;omega) (by change b ≤ w.length-1;omega) e)
  have close : w.getVert 4 = w.getVert 0 := by rw [← len,w.getVert_length,w.getVert_zero]
  have a0 := w.adj_getVert_succ (i:=0) (by omega)
  have a1 := w.adj_getVert_succ (i:=1) (by omega)
  have a2 := w.adj_getVert_succ (i:=2) (by omega)
  have a3 := w.adj_getVert_succ (i:=3) (by omega)
  exact no_square E h _ _ _ _ (nz 0 2 (by decide) (by decide) (by decide))
    (nz 1 3 (by decide) (by decide) (by decide)) ⟨a0,close ▸ a3.symm,a1.symm,a2⟩

end PEqualNP.Research.Girth3321

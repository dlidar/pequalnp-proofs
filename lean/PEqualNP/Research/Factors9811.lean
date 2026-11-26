import Mathlib

namespace PEqualNP.Research.PuncturedFactors
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
abbrev Input := BitVec 14
abbrev V := Fin 14
def edges : List (V × V) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def on (x : Input) (i : V) := x.getLsbD i.val
def mark (x : Input) (i : V) : Input := x ||| ((1 : Input) <<< i.val)
def graph (x : Input) : Bool := edges.any fun p => on x p.1 && on x p.2
def ignores (f : Input → Bool) (i : V) := ∀ x, f (mark x i) = f x

def maximalRows : List Input := [127, 245, 314, 432, 543, 661, 794, 1102, 1220, 1550, 1802, 2087, 2213, 2338, 2567, 2693, 3590, 3716, 4179, 4305, 4627, 4753, 4882, 5008, 5186, 6659, 7938, 8297, 8417, 8488, 8713, 9288, 9992, 10401, 10656, 12481, 13504, 14977, 16256]
def triples : List (V × V × V) := [(0, 8, 10), (1, 3, 7), (1, 7, 13), (5, 6, 9)]
theorem maximal_bounds (x : Input) (h : x ∈ maximalRows) :
    graph x = false ∧ ∀ i : V, on x i = false → graph (mark x i) = true := by
  have cert : maximalRows.all (fun y => !graph y &&
      (List.finRange 14).all (fun i => on y i || graph (mark y i))) = true := by decide +kernel
  have hh := List.all_eq_true.mp cert x h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
  refine ⟨hh.1,?_⟩
  intro i hi
  have v := List.all_eq_true.mp hh.2 i (List.mem_finRange i)
  simpa [hi] using v

def avoids (x : Input) (i j k : V) := !(on x i || on x j || on x k)
theorem triple_obstruction (i j k : V) (ij : i ≤ j) (jk : j ≤ k)
    (bad : (i,j,k) ∉ triples) :
    ∃ x ∈ maximalRows, on x i = false ∧ on x j = false ∧ on x k = false := by
  have cert : ∀ a b c : V, (decide (b < a ∨ c < b ∨ (a,b,c) ∈ triples) ||
      maximalRows.any (fun x => avoids x a b c)) = true := by decide +kernel
  obtain ⟨x,hx,h⟩ := List.any_eq_true.mp (show maximalRows.any (fun x => avoids x i j k) = true by simpa only [Bool.or_eq_true, decide_eq_true_eq, not_lt.mpr ij, not_lt.mpr jk, bad, false_or] using cert i j k)
  exact ⟨x,hx,by simpa [avoids,and_assoc] using h⟩

/-- Three ordered omissions in a conjunctive representation must form one of four triples. -/
theorem necessary_triple (f g h : Input → Bool) (i j k : V) (ij : i ≤ j) (jk : j ≤ k)
    (fi : ignores f i) (gj : ignores g j) (hk : ignores h k)
    (rep : ∀ x, (f x && g x && h x) = graph x) : (i,j,k) ∈ triples := by
  by_contra bad
  obtain ⟨x,m,ni,nj,nk⟩ := triple_obstruction i j k ij jk bad
  obtain ⟨no,up⟩ := maximal_bounds x m
  have lift (y : Input) (hy : graph y = true) : f y = true ∧ g y = true ∧ h y = true := by
    have v := (rep y).trans hy
    simpa [Bool.and_eq_true,and_assoc] using v
  have a := (lift _ (up i ni)).1
  have b := (lift _ (up j nj)).2.1
  have c := (lift _ (up k nk)).2.2
  rw [fi] at a
  rw [gj] at b
  rw [hk] at c
  simpa [a,b,c,no] using rep x

theorem one_factor_full (f g : Input → Bool) (rep : ∀ x, (f x && g x) = graph x) :
    (∀ i, ¬ ignores f i) ∨ (∀ j, ¬ ignores g j) := by
  classical
  by_contra bad
  push Not at bad
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := bad
  have never : ∀ a b : V, (a,a,b) ∉ triples := by decide +kernel
  rcases le_total i j with ij|ji
  · apply never i j
    apply necessary_triple f f g i i j le_rfl ij hi hi hj
    simpa using rep
  · apply never j i
    apply necessary_triple g g f j j i le_rfl ji hj hj hi
    intro x
    simpa [Bool.and_comm] using rep x
theorem cofactor_ignores (i : V) : ignores (fun x => graph (mark x i)) i := by
  intro x
  simp [mark, BitVec.or_assoc]

theorem feasible0 (x : Input) :
    (graph (mark x 0) && graph (mark x 8) && graph (mark x 10)) = graph x := by
  simp only [graph,edges,List.any_cons,List.any_nil,Bool.or_false,on,mark]
  apply Bool.eq_iff_iff.mpr
  norm_num [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one, Fin.val_ofNat, Bool.or_eq_true,Bool.and_eq_true] <;> grind (splits := 80)
theorem feasible1 (x : Input) :
    (graph (mark x 1) && graph (mark x 3) && graph (mark x 7)) = graph x := by
  simp only [graph,edges,List.any_cons,List.any_nil,Bool.or_false,on,mark]
  apply Bool.eq_iff_iff.mpr
  norm_num [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one, Fin.val_ofNat, Bool.or_eq_true,Bool.and_eq_true] <;> grind (splits := 80)
theorem feasible2 (x : Input) :
    (graph (mark x 1) && graph (mark x 7) && graph (mark x 13)) = graph x := by
  simp only [graph,edges,List.any_cons,List.any_nil,Bool.or_false,on,mark]
  apply Bool.eq_iff_iff.mpr
  norm_num [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one, Fin.val_ofNat, Bool.or_eq_true,Bool.and_eq_true] <;> grind (splits := 80)
theorem feasible3 (x : Input) :
    (graph (mark x 5) && graph (mark x 6) && graph (mark x 9)) = graph x := by
  simp only [graph,edges,List.any_cons,List.any_nil,Bool.or_false,on,mark]
  apply Bool.eq_iff_iff.mpr
  norm_num [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one, Fin.val_ofNat, Bool.or_eq_true,Bool.and_eq_true] <;> grind (splits := 80)
end PEqualNP.Research.PuncturedFactors

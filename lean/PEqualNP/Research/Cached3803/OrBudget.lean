import PEqualNP.Research.Cached3803.CachedClauses
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.Research.SelectorBound PEqualNP.Research.FlagGeometry3803 PEqualNP.Research.CachedClauses3803
namespace PEqualNP.Research.OrBudget3803
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
def hit (s : List ℕ) := (univ : Finset (Fin 52)).filter fun i => clause s (posRow i)
theorem raw_cost (a : ℕ) : (hit [a]).card ≤ 4 := by
  if h : a < 26 then
    have exact4 : ∀ u : Fin 26, (hit [u.val]).card = 4 := by decide +kernel
    exact (exact4 ⟨a,h⟩).le
  else
    have empty : hit [a] = ∅ := by
      ext i
      have low : (posRow i).length ≤ a := by simpa [posRow,incidenceInput] using (Nat.le_of_not_gt h)
      simp only [hit,Finset.mem_filter,clause,List.any_cons,List.any_nil,List.getD_eq_default _ _ low]; simp [List.getElem?_eq_none low]
    simp [empty]
theorem hit_count (s : List ℕ) : (hit s).card ≤ 4*s.length := by
  induction s with
  | nil => simp [hit,clause]
  | cons a s ih =>
    have union : hit (a::s) = hit [a] ∪ hit s := by ext; simp [hit,clause]
    have bound := Finset.card_union_le (hit [a]) (hit s)
    have single := raw_cost a
    rw [union,List.length_cons]
    omega
theorem or_count (s : List ℕ) (short : s.length ≤ 4) (C : Circuit) (h : Monotone2 C)
    (pos : ∀ l p, p ∈ singerLines3 l → C.eval (cache s (incidenceInput {p} {l})) = true)
    (neg : ∀ T, IsQuadrangle singerLines3 T → C.eval (cache s (incidenceInput T (missLines singerLines3 T))) = false) :
    6 ≤ total true C.gates := by
  classical
  let G := (univ : Finset (Fin 52)) \ hit s
  have card : 36 ≤ G.card := by
    have bound := hit_count s
    have part := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (hit s))
    change G.card + (hit s).card = _ at part
    simp only [card_univ,Fintype.card_fin] at part
    omega
  let enum := G.orderEmbOfFin rfl
  let r (i : Fin G.card) := cache s (posRow (enum i))
  have silent (i : Fin G.card) : clause s (posRow (enum i)) = false := by
    have mem : enum i ∈ G := G.orderEmbOfFin_mem _ _
    have bad := (Finset.mem_sdiff.mp mem).2
    simpa [hit] using bad
  have power := circuit_packing true C h r (fun i => pos _ _ (flag_ok (enum i))) (by
    intro i j lt
    obtain ⟨k,sep⟩ := positive_meet _ _ (enum.strictMono lt)
    refine ⟨cache s (negRow k),by simp [r,cache,posRow,incidenceInput],by simp [r,cache,posRow,negRow,incidenceInput],?_,by simp [negRow,neg _ (point_ok k)]⟩
    exact append_agree (by simp [posRow,incidenceInput]) (by simp [posRow,negRow,incidenceInput]) sep (by simp [silent i]))
  by_contra! small
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) (show total true C.gates ≤ 5 by omega)
  omega
end PEqualNP.Research.OrBudget3803

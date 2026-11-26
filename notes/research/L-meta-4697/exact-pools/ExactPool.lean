import Charge
import StarPools
namespace PEqualNP.Research.Pool4697
open Finset PEqualNP.MetaComplexity.NestedCover
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem thin_of_girth (h : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) : Thin G := by
  intro a b ne
  by_contra! many
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp many
  obtain ⟨au,bu⟩ := mem_inter.mp hu
  obtain ⟨av,bv⟩ := mem_inter.mp hv
  have au' := (G.mem_neighborFinset _ _).mp au
  have bu' := (G.mem_neighborFinset _ _).mp bu
  have av' := (G.mem_neighborFinset _ _).mp av
  have bv' := (G.mem_neighborFinset _ _).mp bv
  let w : G.Walk a a := .cons au' (.cons bu'.symm (.cons bv' (.cons av'.symm .nil)))
  have cyc : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [w,SimpleGraph.Walk.isPath_def,au'.ne,bu'.ne,av'.ne,bv'.ne,Ne.symm,ne,uv]
    · exact (by decide : 3 ≤ 4)
  have bad := h a w cyc
  change 5 ≤ 4 at bad
  omega

def Represents (B : List (Finset (Fin n))) (m : Nat) (X Y : Fin m → Finset (Fin n)) :=
  Built B ∧ (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
  (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i,x u=true) ∧ ∃ v ∈ Y i,x v=true) ↔
      ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true)

theorem exact_budget [Nonempty (Fin n)] (thin : Thin G) (s : Nat) :
    (∃ B m X Y, Represents G B m X Y ∧ B.length+2*m ≤ s) ↔
    ∃ K : Finset (Fin n), G.IsVertexCover ↑K ∧ G.edgeSet.ncard + K.card ≤ s := by
  constructor
  · rintro ⟨B,m,X,Y,⟨built,av,ok⟩,sz⟩
    obtain ⟨K,c,small,le⟩ := charge G thin B m X Y built av ok
    exact ⟨K,c,by omega⟩
  · rintro ⟨K,c,sz⟩
    obtain ⟨B,m,X,Y,b,av,ok,le⟩ := StarPools4697.build_child n G K (fun _ _ h => c h)
    exact ⟨B,m,X,Y,⟨b,av,ok⟩,le.trans sz⟩

theorem optimal_profile [Nonempty (Fin n)] (thin : Thin G) {K : Finset (Fin n)} (minK : IsMinCover G K)
    {B m X Y} (h : Represents G B m X Y) (best : B.length+2*m ≤ G.edgeSet.ncard + K.card) :
    m = K.card ∧ B.length+m=G.edgeSet.ncard ∧
    ∃ T : Finset (Fin n),IsMinCover G T ∧ T.card=m := by
  obtain ⟨T,c,small,le⟩ := charge G thin B m X Y h.1 h.2.1 h.2.2
  have low := minK.2 T c
  have eq : T.card=K.card := by omega
  exact ⟨by omega,by omega,T,⟨c,fun S s => eq ▸ minK.2 S s⟩,by omega⟩
end PEqualNP.Research.Pool4697

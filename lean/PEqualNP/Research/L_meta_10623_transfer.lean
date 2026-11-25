import PEqualNP.Research.L_meta_10623_separator

namespace PEqualNP.Research.TriangleTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.TriangleChannels PEqualNP.Research.TriangleCosts
open PEqualNP.Research.EncoderBounds PEqualNP.Research.ChannelRouting PEqualNP.Research.TriangleSeparator

def marked (g : Gate) : Bool := match g.op with | .not => true | _ => false
def nots (gs : List Gate) := gs.countP marked

def bowWitness := ∃ D : Circuit, legal D.gates ∧ nots D.gates ≤ 1 ∧ D.size ≤ 7 ∧
  ∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = bow (x 0) (x 1,x 2) (x 3,x 4)

def separatedWitness := ∃ (g h : List Gate) (l r : ℕ × ℕ) (D : Circuit),
    legal g ∧ legal h ∧ legal D.gates ∧ nots g + nots h + nots D.gates ≤ 1 ∧
    Monotone (encode g l.1 l.2) ∧ Monotone (encode h r.1 r.2) ∧
    g.length + h.length + D.size ≤ 13 ∧
    ∀ x y z, D.eval (word z (encode g l.1 l.2 x) (encode h r.1 r.2 y)) = f x y z

theorem route_legal (a b : Tri) (D : Circuit) (h : legal D.gates) :
    legal (extend (prep a b) (index a b) D).gates := by
  intro t ht
  rcases List.mem_append.mp ht with hp | hd
  · obtain ⟨op,sz⟩ := prep_legal a b t hp
    have dis : t.op = .and ∨ t.op = .or := op
    exact ⟨dis.imp_right Or.inl,sz⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hd
    simpa [allowed,ChannelRouting.trans] using h g hg

theorem inv_cost_pre : ∀ a b, nots (prep a b) = 0 := by decide +kernel

theorem inv_cost_route (a b : Tri) (D : Circuit) :
    nots (extend (prep a b) (index a b) D).gates = nots D.gates := by
  change (prep a b ++ D.gates.map _).countP marked = _
  rw [List.countP_append,show (prep a b).countP marked = 0 from inv_cost_pre a b,Nat.zero_add,List.countP_map]
  rfl

theorem exact_transfer : separatedWitness ↔ bowWitness := by
  constructor
  · rintro ⟨g,h,l,r,D,lg,lh,ld,inv,mg,mh,small,fits⟩
    let p := encode g l.1 l.2
    let q := encode h r.1 r.2
    have pp : sufficient p := side_sufficient p q (fun a b z => D.eval (word z a b)) fits
    have qq : sufficient q := side_sufficient q p (fun b a z => D.eval (word z a b))
      (fun x y z => by rw [fits]; simp [f,Bool.or_comm])
    let a : Tri := fun i => (p (single i)).1
    let b : Tri := fun i => (q (single i)).1
    have hp : p = colored a := classified p pp mg
    have hq : q = colored b := classified q qq mh
    have eg := encoder_budget a g lg l.1 l.2 (congrFun hp)
    have eh := encoder_budget b h lh r.1 r.2 (congrFun hq)
    refine ⟨extend (prep a b) (index a b) D, route_legal a b D ld, ?_, ?_, ?_⟩
    · rw [inv_cost_route]; omega
    · rw [extend_size,prep_size]; omega
    · exact routed_exact a b D (fun x y z => by rw [←hp,←hq]; exact fits x y z)
  · rintro ⟨D,ld,inv,small,correct⟩
    have lg : legal splitGates := by
      intro g h
      simp only [splitGates,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [allowed]
    let c : Tri := ![true,true,false]
    have eq : encode splitGates 3 5 = colored c := funext split_sharp.2
    refine ⟨splitGates,splitGates,(3,5),(3,5),D,lg,lg,ld,?_,?_,?_,?_,?_⟩
    · simpa [nots,splitGates,marked] using inv
    · rw [eq]; exact color_mono c
    · rw [eq]; exact color_mono c
    · rw [split_sharp.1]; omega
    · intro x y z
      rw [eq]
      let p := colored c x
      let q := colored c y
      let xx : Fin 5 → Bool := ![z,p.1,p.2,q.1,q.2]
      have wire : List.ofFn xx = word z p q := rfl
      change D.eval (word z p q) = _
      rw [←wire,correct]
      exact bow_exact c c x y z

end PEqualNP.Research.TriangleTransfer

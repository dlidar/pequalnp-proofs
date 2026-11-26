import Assemble
namespace PHPOverlap
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
theorem parent_leaves {C : ClauseMap Grid} {P : Parents} {r c : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hc : c < r) (edge : c ∈ P r) :
    WithArity P c 0 ⊆ WithArity P r 0 := by
  intro j h
  obtain ⟨live,zero⟩ := Finset.mem_filter.mp h
  have w := (live_iff (fun i hi => rules i (hi.trans hc.le))).mp live
  have w' : Walk (LocalEdge P r) c j := walk_sub (fun e => ⟨e.1.trans hc.le,e.2⟩) w
  have fromRoot : Walk (LocalEdge P r) r j := Relation.ReflTransGen.head ⟨le_rfl,edge⟩ w'
  exact Finset.mem_filter.mpr ⟨(live_iff rules).mpr fromRoot,zero⟩

theorem shared_surplus {C : ClauseMap Grid} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hc : c < r) (hd : d < r) (ne : c ≠ d)
    (pc : c ∈ P r) (pd : d ∈ P r) (h : (Live P c ∩ Live P d).Nonempty) : 1 ≤ Surplus P r := by
  obtain ⟨x,hx⟩ := h
  have rc : LocalEdge P r r c := ⟨le_rfl,pc⟩
  have rd : LocalEdge P r r d := ⟨le_rfl,pd⟩
  obtain ⟨lc,ld⟩ := Finset.mem_inter.mp hx
  have wc := (live_iff (fun i hi => rules i (hi.trans hc.le))).mp lc
  have wd := (live_iff (fun i hi => rules i (hi.trans hd.le))).mp ld
  obtain ⟨p,q,m,wp,wq,ep,eq,n,_,wm,_⟩ := clash (bounded_edge rules) rc rd ne (A := fun _ => True) trivial
    (walk_sub (fun e => ⟨⟨e.1.trans hc.le,e.2⟩,trivial⟩) wc)
    (walk_sub (fun e => ⟨e.1.trans hd.le,e.2⟩) wd)
  have up {t j : Nat} (e : LocalEdge P r r t) (w : j = r ∨ Walk (LocalEdge P r) t j) : j ∈ Live P r := by
    apply (live_iff rules).2
    rcases w with rfl | w
    · exact .refl
    · exact .head e w
  have degree := shared_degree (up rc wp) (up rd wq) ep.2 eq.2 n
  have mr : m ≠ r := ne_of_lt ((walk_le (bounded_edge rules) wm).trans_lt hc)
  have mem : m ∈ (Live P r).erase r := Finset.mem_erase.mpr ⟨mr,up rc (Or.inr wm)⟩
  have bound := Finset.single_le_sum (f := fun j => InDegree P (Live P r) j - 1) (fun j _ => Nat.zero_le _) mem
  unfold Surplus
  omega

theorem both_counts (rich : ∀ f : Finset Grid, f ≠ ∅ → Rich f)
    (π : List (LinClause Grid)) (refute : IsLinRefutation (PHP 4 3) π) (short : π.length ≤ 51) :
    ∃ C P r c d, Encoded F C P π ∧ r < π.length ∧ P r = [c,d] ∧ c ≠ d ∧
      (∀ a, FalseAt C a r) ∧ 10 ≤ (Live P c ∩ Live P d).card ∧
      6 ≤ (WithArity P c 0 ∩ WithArity P d 0).card ∧
      10 + (WithArity P r 1).card + Surplus P r ≤ 2*(WithArity P c 0 ∩ WithArity P d 0).card := by
  obtain ⟨C,P,graph⟩ := build_graph refute.1
  obtain ⟨r,lt,fr,_,c,hc,d,hd,neq,parents,f,ne,side⟩ := first_false graph refute.2 sat_ax
  have rule : ∀ i ≤ r, Rule F C P i := fun i hi => graph.1 i (hi.trans_lt lt)
  obtain ⟨n,k,total,⟨a,pa,da⟩,⟨b,pb,db⟩⟩ := rich f ne
  have lo := packed_leaves (fun i hi => rule i (hi.trans hd.le)) a (by
    intro t; have h := side (a t); have p := pa t
    split at h <;> simp_all [OddAt]) (fun i j ne => sat_of_apart (da i j ne))
  have hi := packed_leaves (fun i hi => rule i (hi.trans hc.le)) b (by
    intro t; have h := side (b t); have p := pb t
    split at h <;> simp_all [OddAt]) (fun i j ne => sat_of_apart (db i j ne))
  have count := overlap_bound rule hc hd hi lo
  have sub := Finset.union_subset (parent_leaves rule hc (by simp [parents])) (parent_leaves rule hd (by simp [parents]))
  have ca := Finset.card_le_card sub
  have ar := arity_count rule
  have sz := live_card_le P r
  have id := Finset.card_union_add_card_inter (WithArity P c 0) (WithArity P d 0)
  have cardpos : 0 < (Live P c ∩ Live P d).card := by omega
  have surplus := shared_surplus rule hc hd neq (by simp [parents]) (by simp [parents]) (Finset.card_pos.mp cardpos)
  exact ⟨C,P,r,c,d,graph,lt,parents,neq,fr,by omega,by omega,by omega⟩
end PHPOverlap

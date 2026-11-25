import PEqualNP.Outside.L_meta_702
import PEqualNP.Research.L_meta_10623_encoders
import PEqualNP.Research.L_meta_10623_routing

namespace PEqualNP.Research.TriangleSeparator
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.TriangleChannels PEqualNP.Research.TriangleCosts PEqualNP.Research.EncoderBounds
open PEqualNP.Research.ChannelRouting

def mapCode (c : Tri) (p : Pair) : Pair :=
  if sortCost c = 0 then p else
    if c 0 then (p.1 || p.2,p.1 && p.2) else (p.1 && p.2,p.1 || p.2)

theorem realize : ∀ c p, ∃ x, colored c x = mapCode c p ∧
    low x = (p.1 || p.2) ∧ high x = (p.1 && p.2) := by decide +kernel

def sortG (c : Tri) (i j : ℕ) : List Gate :=
  if sortCost c = 0 then [] else [⟨.or,[i,j]⟩,⟨.and,[i,j]⟩]
def aliases (c : Tri) (i j start : ℕ) : ℕ × ℕ :=
  if sortCost c = 0 then (i,j) else if c 0 then (start,start+1) else (start+1,start)
def prep (a b : Tri) := sortG a 1 2 ++ sortG b 3 4
def access (a b : Tri) :=
  let l := aliases a 1 2 5
  let r := aliases b 3 4 (5 + sortCost a)
  [0,l.1,l.2,r.1,r.2]
def index (a b : Tri) (i : ℕ) :=
  if i < 5 then (access a b).getD i 0 else i+(prep a b).length

def word (z : Bool) (p q : Pair) := [z,p.1,p.2,q.1,q.2]

theorem prep_size : ∀ a b, (prep a b).length = sortCost a + sortCost b := by decide +kernel

theorem prep_legal (a b : Tri) : Monotone2 ⟨prep a b,0⟩ := by
  have ok (c : Tri) (i j : ℕ) : Monotone2 ⟨sortG c i j,0⟩ := by
    intro g hg
    change g ∈ sortG c i j at hg
    by_cases h : sortCost c = 0
    · simp [sortG,h] at hg
    · simp only [sortG,h,ite_false,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl <;> simp
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ok a 1 2 g h
  · exact ok b 3 4 g h

theorem index_lt : ∀ a b (i : Fin 5), index a b i < 5 + (prep a b).length := by decide +kernel

theorem raw_eval : ∀ a b (x : Fin 5 → Bool) (i : Fin 5),
    (word (x 0) (mapCode a (x 1,x 2)) (mapCode b (x 3,x 4))).getD i false =
    (ChannelRouting.run (prep a b) (List.ofFn x)).getD (index a b i) false := by decide +kernel

theorem raw_length : ∀ a b (x : Fin 5 → Bool),
    (ChannelRouting.run (prep a b) (List.ofFn x)).length = 5+(prep a b).length := by decide +kernel

def bowEdge (x : Fin 5 → Bool) : Prop :=
  ∃ u v : Fin 5, (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true

theorem bow_edge : ∀ x : Fin 5 → Bool, bow (x 0) (x 1,x 2) (x 3,x 4) = true ↔ bowEdge x := by
  unfold bowEdge
  decide +kernel

theorem routed_exact (a b : Tri) (D : Circuit)
    (fits : ∀ x y z, D.eval (word z (colored a x) (colored b y)) = f x y z)
    (x : Fin 5 → Bool) :
    (extend (prep a b) (index a b) D).eval (List.ofFn x) = bow (x 0) (x 1,x 2) (x 3,x 4) := by
  let E := extend (prep a b) (index a b) D
  let u := word (x 0) (mapCode a (x 1,x 2)) (mapCode b (x 3,x 4))
  have conv := extend_eval (prep a b) (index a b) D (List.ofFn x) u
    (fun i hi => index_lt a b ⟨i,hi⟩) (fun i hi => by simp [index,Nat.not_lt_of_ge hi])
    (by rfl) (raw_length a b x) (by
      intro i
      by_cases h : i < 5
      · exact raw_eval a b x ⟨i,h⟩
      · rw [List.getD_eq_default _ _ (by change 5 ≤ i; omega),List.getD_eq_default _ _ (by
          rw [raw_length]; simp [index,h]; omega)])
  obtain ⟨l,hc,hl,hh⟩ := realize a (x 1,x 2)
  obtain ⟨r,kc,kl,kh⟩ := realize b (x 3,x 4)
  rw [show E.eval _ = D.eval u from conv]
  dsimp [u]
  rw [←hc,←kc,fits]
  simp [f,bow,hl,hh,kl,kh,Bool.or_assoc]

theorem decoder_budget (a b : Tri) (D : Circuit) (md : Monotone2 D)
    (fits : ∀ x y z, D.eval (word z (colored a x) (colored b y)) = f x y z) :
    8 ≤ D.size + sortCost a + sortCost b := by
  let E := extend (prep a b) (index a b) D
  have bound := PEqualNP.Outside.L_meta_702 E (extend_mono _ _ _ (prep_legal a b) md)
    (fun x => by change (extend _ _ _).eval _ = true ↔ _; rw [routed_exact a b D fits]; exact bow_edge x)
  change 8 ≤ (extend _ _ _).size at bound
  rw [extend_size,prep_size] at bound
  omega

theorem separated_lower (g h : List Gate) (gm hm : ℕ × ℕ) (D : Circuit)
    (lg : legal g) (lh : legal h) (md : Monotone2 D)
    (ig : Monotone (encode g gm.1 gm.2)) (ih : Monotone (encode h hm.1 hm.2))
    (computes : ∀ x y z, D.eval (word z (encode g gm.1 gm.2 x) (encode h hm.1 hm.2 y)) = f x y z) :
    14 ≤ g.length + h.length + D.size := by
  let p := encode g gm.1 gm.2
  let q := encode h hm.1 hm.2
  have pp : sufficient p := side_sufficient p q (fun a b z => D.eval (word z a b)) computes
  have qq : sufficient q := side_sufficient q p (fun b a z => D.eval (word z a b))
    (fun x y z => by rw [computes]; simp [f,Bool.or_comm])
  let a : Tri := fun i => (p (single i)).1
  let b : Tri := fun i => (q (single i)).1
  have hp : p = colored a := classified p pp ig
  have hq : q = colored b := classified q qq ih
  have lg' := encoder_budget a g lg gm.1 gm.2 (congrFun hp)
  have lh' := encoder_budget b h lh hm.1 hm.2 (congrFun hq)
  have hd := decoder_budget a b D md (fun x y z => by rw [←hp,←hq]; exact computes x y z)
  omega


def sortedDecoder : Circuit :=
  ⟨[⟨.or,[1,3]⟩,⟨.and,[0,5]⟩,⟨.or,[2,4]⟩,⟨.or,[6,7]⟩],8⟩

theorem sorted_exact : ∀ x y z, sortedDecoder.eval
    (word z (encode sortedGates 7 6 x) (encode sortedGates 7 6 y)) = f x y z := by decide +kernel

theorem sorted_mono : Monotone2 sortedDecoder ∧ Monotone2 ⟨sortedGates,7⟩ := by
  constructor
  · intro g hg
    simp only [sortedDecoder,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro g hg
    simp only [sortedGates,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem sorted_cost : sortedGates.length + sortedGates.length + sortedDecoder.size = 14 := rfl

end PEqualNP.Research.TriangleSeparator

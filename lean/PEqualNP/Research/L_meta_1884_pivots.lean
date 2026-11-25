import Mathlib

namespace PEqualNP.Research.PetersenPivots
open Finset

section General
variable {V : Type} [DecidableEq V] (E : V → V → Prop)
def Hit (S : Finset V) := ∃ u ∈ S, ∃ v ∈ S, E u v
def Pivot (i : V) (on off : Finset V) := ∃ S : Finset V,
  on ⊆ S ∧ Disjoint S off ∧ i ∉ S ∧ ¬ Hit E S ∧ Hit E (insert i S)

theorem hit_insert (sym : ∀ ⦃u v⦄, E u v → E v u) (loop : ∀ v, ¬ E v v) (i : V) (S : Finset V) :
    Hit E (insert i S) ↔ Hit E S ∨ ∃ j ∈ S, E i j := by
  simp only [Hit,mem_insert]
  constructor
  · rintro ⟨a,ha,b,hb,e⟩
    rcases ha with rfl|ha <;> rcases hb with rfl|hb
    · exact (loop _ e).elim
    · exact Or.inr ⟨_,hb,e⟩
    · exact Or.inr ⟨_,ha,sym e⟩
    · exact Or.inl ⟨_,ha,_,hb,e⟩
  · rintro (⟨a,ha,b,hb,e⟩|⟨j,hj,e⟩)
    · exact ⟨a,Or.inr ha,b,Or.inr hb,e⟩
    · exact ⟨i,Or.inl rfl,j,Or.inr hj,e⟩

theorem pivot_iff (sym : ∀ ⦃u v⦄, E u v → E v u) (loop : ∀ v, ¬ E v v) (i : V) (on off : Finset V)
    (free : i ∉ on) (compatible : Disjoint on off) :
    Pivot E i on off ↔ ¬ Hit E on ∧ ∃ j, E i j ∧ j ∉ off ∧ ∀ k ∈ on, ¬ E j k := by
  constructor
  · rintro ⟨S,inc,dis,_,neg,pos⟩
    obtain ⟨j,hj,e⟩ := ((hit_insert E sym loop i S).mp pos).resolve_left neg
    exact ⟨fun ⟨a,ha,b,hb,f⟩ => neg ⟨a,inc ha,b,inc hb,f⟩,j,e,disjoint_left.mp dis hj,
      fun k hk f => neg ⟨j,hj,k,inc hk,f⟩⟩
  · rintro ⟨neg,j,e,allowed,clean⟩
    have ne : i ≠ j := fun h => loop j (h ▸ e)
    refine ⟨insert j on,subset_insert _ _,disjoint_left.mpr ?_,by simp [ne,free],?_,?_⟩
    · intro k h; rcases mem_insert.mp h with rfl|h
      · exact allowed
      · exact disjoint_left.mp compatible h
    · rw [hit_insert E sym loop]
      exact fun h => h.elim neg (fun ⟨k,hk,f⟩ => clean k hk f)
    · exact (hit_insert E sym loop _ _).mpr (Or.inr ⟨j,mem_insert_self _ _,e⟩)
end General

abbrev V := Fin 10
def adj (i j : V) : Bool := (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val
theorem symm : ∀ i j, adj i j = adj j i := by decide +kernel
theorem irref : ∀ i, adj i i = false := by decide +kernel
abbrev E (i j : V) := adj i j = true
theorem symE : ∀ ⦃u v⦄, E u v → E v u := fun i j e => (symm j i).trans e
theorem irE : ∀ v, ¬ E v v := by intro i; simp [E,irref]

-- Each neighbor j is blocked by pinning j off or one of its other neighbors on.
abbrev Pin := V × Bool
def blockedBy (i j : V) (p : Pin) := if p.2 then p.1 ≠ i ∧ E j p.1 else p.1 = j
instance (i j : V) (p : Pin) : Decidable (blockedBy i j p) := by unfold blockedBy; infer_instance
def arms (i j : V) := univ.filter (blockedBy i j)
def pins (on off : Finset V) : Finset Pin :=
  (on.image fun x => (x,true)) ∪ (off.image fun x => (x,false))
theorem arms_hit (i j : V) (on off : Finset V) (free : i ∉ on) :
    (∃ t ∈ arms i j, t ∈ pins on off) ↔ j ∈ off ∨ ∃ k ∈ on, E j k := by
  constructor
  · rintro ⟨⟨k,b⟩,h,p⟩
    cases b <;> simp_all [arms,blockedBy,pins]
    exact Or.inr ⟨k,p,h.2⟩
  · rintro (h|⟨k,hk,e⟩)
    · exact ⟨(j,false),by simp [arms,blockedBy],by simp [pins,h]⟩
    · have ne : k ≠ i := fun eq => free (eq ▸ hk)
      exact ⟨(k,true),by simpa [arms,blockedBy,ne] using e,by simp [pins,hk]⟩

def neighbors (i : V) := (List.finRange 10).filter (adj i)
def nb (i : V) (j : ℕ) := (neighbors i).getD j 0
theorem nb_spec : ∀ i j, E i j ↔ j = nb i 0 ∨ j = nb i 1 ∨ j = nb i 2 := by decide +kernel

def triples (i : V) : Finset (Finset Pin) :=
  (((arms i (nb i 0)).product (arms i (nb i 1))).product (arms i (nb i 2))).image
    (fun q => {q.1.1,q.1.2,q.2})
theorem obstruction_iff (i : V) (on off : Finset V) (free : i ∉ on)
    (c : Disjoint on off) (ind : ¬ Hit E on) :
    ¬ Pivot E i on off ↔ ∃ T ∈ triples i, T ⊆ pins on off := by
  rw [pivot_iff E symE irE i on off free c]
  rw [and_iff_right ind]
  push Not
  constructor
  · intro h
    have one (t : ℕ) (e : E i (nb i t)) : ∃ p ∈ arms i (nb i t), p ∈ pins on off := by
      apply (arms_hit _ _ _ _ free).mpr
      by_cases bad : nb i t ∈ off
      · exact Or.inl bad
      · exact Or.inr (h _ e bad)
    obtain ⟨x,hx,px⟩ := one 0 ((nb_spec _ _).mpr (Or.inl rfl))
    obtain ⟨y,hy,py⟩ := one 1 ((nb_spec _ _).mpr (Or.inr (Or.inl rfl)))
    obtain ⟨z,hz,pz⟩ := one 2 ((nb_spec _ _).mpr (Or.inr (Or.inr rfl)))
    refine ⟨{x,y,z},mem_image.mpr ⟨((x,y),z),mem_product.mpr ⟨mem_product.mpr ⟨hx,hy⟩,hz⟩,rfl⟩,?_⟩
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl|rfl <;> assumption
  · rintro ⟨_,ht,sub⟩ j e ok
    by_contra! clean
    obtain ⟨⟨⟨x,y⟩,z⟩,mem,rfl⟩ := mem_image.mp ht
    obtain ⟨hxy,hz⟩ := mem_product.mp mem
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    have bad (t : Pin) (ht : t ∈ arms i j) (hp : t ∈ pins on off) : False := by
      rcases (arms_hit _ _ _ _ free).mp ⟨t,ht,hp⟩ with h|⟨k,hk,h⟩
      · exact ok h
      · exact clean k hk h
    rcases (nb_spec _ _).mp e with rfl|rfl|rfl
    · exact bad x hx (sub (by simp))
    · exact bad y hy (sub (by simp))
    · exact bad z hz (sub (by simp))

def feasible (T : Finset Pin) := ∀ a ∈ T, ∀ b ∈ T, a.2 = true → b.2 = true → adj a.1 b.1 = false
instance (T : Finset Pin) : Decidable (feasible T) := by unfold feasible; infer_instance
def minimalBlocks (i : V) := (triples i).filter feasible
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
theorem triple_sizes (i : V) (T : Finset Pin) (ht : T ∈ triples i) : T.card = 3 := by
  have cert : ∀ j : V, ((triples j).filter fun U => U.card ≠ 3) = ∅ := by decide +kernel
  by_contra bad
  have mem : T ∈ (triples i).filter (fun U => U.card ≠ 3) := mem_filter.mpr ⟨ht,bad⟩
  rw [cert] at mem
  exact notMem_empty _ mem
theorem profile : ∀ i, (minimalBlocks i).card = 15 ∧
    ∀ k : Fin 4, ((minimalBlocks i).filter (fun T => (T.filter (fun p => p.2)).card = k.val)).card =
      ([1,6,6,2] : List ℕ).getD k.val 0 := by decide +kernel
theorem feasible_classification (i : V) (on off : Finset V) (free : i ∉ on)
    (c : Disjoint on off) (ind : ¬ Hit E on) :
    ¬ Pivot E i on off ↔ ∃ T ∈ minimalBlocks i, T ⊆ pins on off := by
  rw [obstruction_iff i on off free c ind]
  constructor
  · rintro ⟨T,hT,sub⟩
    refine ⟨T,mem_filter.mpr ⟨hT,?_⟩,sub⟩
    rintro ⟨a,ba⟩ ha ⟨b,bb⟩ hb ea eb
    change ba = true at ea
    change bb = true at eb
    subst ba; subst bb
    have ha' : a ∈ on := by simpa [pins] using sub ha
    have hb' : b ∈ on := by simpa [pins] using sub hb
    cases h : adj a b
    · rfl
    · exact (ind ⟨a,ha',b,hb',h⟩).elim
  · rintro ⟨T,hT,sub⟩
    exact ⟨T,(mem_filter.mp hT).1,sub⟩

theorem two_pins (i : V) (on off : Finset V) (free : i ∉ on)
    (c : Disjoint on off) (ind : ¬ Hit E on) (small : (pins on off).card ≤ 2) : Pivot E i on off := by
  by_contra hn
  obtain ⟨T,hT,sub⟩ := (obstruction_iff i on off free c ind).mp hn
  have := card_le_card sub
  rw [triple_sizes i T hT] at this
  omega

def val (S : Finset V) (v : V) := decide (v ∈ S)

theorem pivot_values (i : V) (on off : Finset V) (h : Pivot E i on off) :
    ∃ x : V → Bool, (∀ k ∈ on, x k = true) ∧ (∀ k ∈ off, x k = false) ∧
      ∀ z : Bool, decide (∃ u v, Function.update x i z u = true ∧
        Function.update x i z v = true ∧ adj u v = true) = z := by
  obtain ⟨S,inc,dis,free,neg,pos⟩ := h
  refine ⟨val S,fun k hk => decide_eq_true (inc hk),?_,?_⟩
  · intro k hk
    exact decide_eq_false (fun mem => disjoint_left.mp dis mem hk)
  · have zero : Function.update (val S) i false = val S := by
      funext k; by_cases e : k = i <;> simp [Function.update,val,e,free]
    have one : Function.update (val S) i true = val (insert i S) := by
      funext k; by_cases e : k = i <;> simp [Function.update,val,e]
    intro z
    cases z
    · rw [zero]
      apply decide_eq_false
      rintro ⟨u,v,hu,hv,e⟩
      exact neg ⟨u,of_decide_eq_true hu,v,of_decide_eq_true hv,e⟩
    · rw [one]
      obtain ⟨u,hu,v,hv,e⟩ := pos
      exact decide_eq_true ⟨u,v,decide_eq_true hu,decide_eq_true hv,e⟩

theorem pivotal (i j k : V) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (good : ¬ (a = true ∧ b = true ∧ adj j k = true)) :
    ∃ x : V → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool,
      decide (∃ p l : V, Function.update x i z p = true ∧ Function.update x i z l = true ∧
        adj p l = true) = z := by
  let on : Finset V := (if a then {j} else ∅) ∪ (if b then {k} else ∅)
  let off : Finset V := (if a then ∅ else {j}) ∪ (if b then ∅ else {k})
  have free : i ∉ on := by cases a <;> cases b <;> simp [on,ij,ik]
  have comp : Disjoint on off := by cases a <;> cases b <;> simp [on,off,jk,Ne.symm jk]
  have ind : ¬ Hit E on := by
    rintro ⟨u,hu,v,hv,edge⟩
    cases a <;> cases b <;> simp [on] at hu hv good <;> grind [irE,symE]
  have small : (pins on off).card ≤ 2 := by
    have sub : pins on off ⊆ {(j,a),(k,b)} := by
      intro w hw
      cases a <;> cases b <;> simp_all [on,off,pins] <;> grind
    exact (card_le_card sub).trans (by simpa using card_insert_le (j,a) {(k,b)})
  obtain ⟨x,onv,offv,piv⟩ := pivot_values i on off (two_pins i on off free comp ind small)
  refine ⟨x,?_,?_,piv⟩
  · cases a <;> [apply offv; apply onv] <;> simp [on,off]
  · cases b <;> [apply offv; apply onv] <;> simp [on,off]

def ones (T : Finset Pin) := (T.filter (fun p => p.2)).image Prod.fst
def zeros (T : Finset Pin) := (T.filter (fun p => !p.2)).image Prod.fst

theorem realized (i : V) (T : Finset Pin) (h : T ∈ minimalBlocks i) :
    i ∉ ones T ∧ i ∉ zeros T ∧ Disjoint (ones T) (zeros T) ∧
    ¬ Hit E (ones T) ∧ pins (ones T) (zeros T) = T ∧ ¬ Pivot E i (ones T) (zeros T) := by
  let consistent (j : V) (U : Finset Pin) : Bool := decide (j ∉ ones U ∧ j ∉ zeros U ∧
    Disjoint (ones U) (zeros U) ∧ pins (ones U) (zeros U) = U)
  have checked : ∀ j : V, ((minimalBlocks j).filter fun U => !consistent j U) = ∅ := by
    dsimp only [consistent]
    decide +kernel
  have yes : consistent i T := by
    by_contra! no
    have mem : T ∈ (minimalBlocks i).filter (fun U => !consistent i U) :=
      mem_filter.mpr ⟨h,by simp_all⟩
    rw [checked] at mem
    exact notMem_empty _ mem
  obtain ⟨free,free',dis,eq⟩ := of_decide_eq_true yes
  have ind : ¬ Hit E (ones T) := by
    rintro ⟨u,hu,v,hv,edge⟩
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hu
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := mem_image.mp hv
    have no := (mem_filter.mp h).2 _ (mem_filter.mp hab).1 _ (mem_filter.mp hcd).1
      (mem_filter.mp hab).2 (mem_filter.mp hcd).2
    exact Bool.noConfusion (edge.symm.trans no)
  exact ⟨free,free',dis,ind,eq,(feasible_classification _ _ _ free dis ind).mpr ⟨T,h,eq.ge⟩⟩

end PEqualNP.Research.PetersenPivots

import Leaves
namespace InverterBridge
open Finset PEqualNP.Research.TripleFormulaMass
variable {I : Type} [DecidableEq I] [Fintype I] [Nonempty I]

theorem pair_cover (S : Finset I) (bound : S.card≤2) : ∃ i j : I, ∀ x∈S,x=i ∨ x=j := by
  classical
  by_cases h : S.Nonempty
  · obtain ⟨i,hi⟩ := h
    have small : (S.erase i).card≤1 := by rw [card_erase_of_mem hi]; omega
    obtain ⟨j,hj⟩ := card_le_one_iff_subset_singleton.mp small
    exact ⟨i,j,fun x hx => or_iff_not_imp_left.mpr (fun ne => mem_singleton.mp (hj (mem_erase.mpr ⟨ne,hx⟩)))⟩
  · exact ⟨Classical.arbitrary I, Classical.arbitrary I, fun x hx => False.elim (h ⟨x,hx⟩)⟩

inductive Value (I : Type) where
  | fixed (b : Bool)
  | term (f : Formula I)

namespace Value
def eval (x : X I) : Value I → Bool
  | .fixed b => b
  | .term f => f.eval x
def leaves : Value I → Nat
  | .fixed _ => 0
  | .term f => f.leaves
def meet (f : Formula I) : Value I → Value I
  | .fixed false => .fixed false
  | .fixed true => .term f
  | .term g => .term (.conj f g)
def join (f : Formula I) : Value I → Value I
  | .fixed false => .term f
  | .fixed true => .fixed true
  | .term g => .term (.disj f g)
theorem meet_eval (f : Formula I) (v : Value I) (x : X I) : (meet f v).eval x = (f.eval x && v.eval x) := by
  cases v with
  | fixed b => cases b <;> simp [meet,eval]
  | term g => rfl
theorem join_eval (f : Formula I) (v : Value I) (x : X I) : (join f v).eval x = (f.eval x || v.eval x) := by
  cases v with
  | fixed b => cases b <;> simp [join,eval]
  | term g => rfl
theorem meet_count (f : Formula I) (v : Value I) : (meet f v).leaves≤f.leaves+v.leaves := by
  cases v with
  | fixed b => cases b <;> simp [leaves,meet]
  | term g => rfl
theorem join_count (f : Formula I) (v : Value I) : (join f v).leaves≤f.leaves+v.leaves := by
  cases v with
  | fixed b => cases b <;> simp [leaves,join]
  | term g => rfl
def pick (k : Fin 4) (i j : I) : Value I := if k=0 then .fixed false else if k=1 then .fixed true else if k=2 then .term (.var i) else .term (.var j)
theorem pick_eval (k : Fin 4) (i j : I) (x : X I) : (pick k i j).eval x = choose k (x i,x j) := by fin_cases k <;> rfl
theorem pick_count (k : Fin 4) (i j : I) : (pick k i j).leaves≤1 := by fin_cases k <;> first | exact Nat.zero_le _ | exact le_rfl
end Value

namespace Context
def plug (v : Value I) : Context I → Value I
  | .hole => v
  | .meet f c => (c.plug v).meet f
  | .join f c => (c.plug v).join f

theorem plug_eval (c : Context I) (v : Value I) (x : X I) : (c.plug v).eval x=c.eval x (v.eval x) := by
  induction c with
  | hole => rfl
  | meet f c ih => simp [plug,Value.meet_eval,ih,eval]
  | join f c ih => simp [plug,Value.join_eval,ih,eval]
theorem plug_count (c : Context I) (v : Value I) : (c.plug v).leaves≤c.rawLeaves+v.leaves := by
  induction c with
  | hole => simp [plug,rawLeaves]
  | meet f c ih => simpa only [plug,rawLeaves,Nat.add_assoc] using (Value.meet_count f (c.plug v)).trans (Nat.add_le_add_left ih _)
  | join f c ih => simpa only [plug,rawLeaves,Nat.add_assoc] using (Value.join_count f (c.plug v)).trans (Nat.add_le_add_left ih _)

theorem small_decoder (c : Context I) (G : X I → Bool) (anti : Antitone G)
    (mono : Monotone (fun x => c.eval x (G x)))
    (essential : ∀ i, ∃ x y : X I,x≤y ∧ (∀ j,j≠i → x j=y j) ∧ c.eval x (G x)=false ∧ c.eval y (G y)=true)
    (small : c.rawLeaves≤Fintype.card I+2) :
    ∃ f : Formula I, f.leaves≤c.rawLeaves+1 ∧ ∀ x,f.eval x=c.eval x (G x) := by
  classical
  have count := c.mixed_count anti essential
  obtain ⟨i,j,pair⟩ := pair_cover (c.posVars ∩ c.negVars) (by omega)
  obtain ⟨k,hk⟩ := c.eliminate G anti mono i j (fun t hp hq => pair t (mem_inter.mpr ⟨hp,hq⟩))
  let v := Value.pick k i j
  have ev (x : X I) : (c.plug v).eval x=c.eval x (G x) := by rw [c.plug_eval,Value.pick_eval]; exact (hk x).symm
  have ct := (c.plug_count v).trans (Nat.add_le_add_left (Value.pick_count k i j) _)
  cases eq : c.plug v with
  | fixed b =>
    obtain ⟨x,y,_,_,h0,h1⟩ := essential i
    have e0 := ev x; have e1 := ev y
    rw [eq,h0] at e0; rw [eq,h1] at e1
    exact False.elim (Bool.noConfusion (e0.symm.trans e1))
  | term f =>
    exact ⟨f,by simpa [eq,Value.leaves] using ct,fun x => by simpa [eq,Value.eval] using ev x⟩
end Context
end InverterBridge

import FactorCriterion
namespace PlaneMask
abbrev Byte := Fin 256
abbrev Cell := Fin 64
def target (a : Cell) := (1885146376704737940 : Nat).testBit a.val = true
def send (s : Byte) (i : Nat) (j : Fin 8) := s.val.testBit i && decide (j.val = i)
def obs (r c : Byte) (a : Cell) := (send r (a.val/8),send c (a.val%8))
def rev (s : Byte) : Byte := ⟨255-s.val, by omega⟩
def Fits (r c : Byte) := SplitMonotoneFactor.Factors (obs r c) (obs (rev r) (rev c)) target
def simple (s : Byte) (i j : Nat) := (i == j) || !(s.val.testBit i)
theorem mono_signal (s : Byte) (i j : Nat) (h : simple s i j = true) : send s i ≤ send s j := by
  simp [simple] at h
  rcases h with rfl | h
  · exact le_rfl
  · intro k
    simp [send,h]
structure Rule where
  a : Cell
  b : Cell
  c : Cell
  d : Cell
  rb : BitVec 256
  cb : BitVec 256

def hit (t : Rule) (s : Byte) (ix : Cell → Nat) :=
  simple (rev s) (ix t.a) (ix t.b) && simple (rev s) (ix t.c) (ix t.d) && simple s (ix t.a) (ix t.d)
def labels (t : Rule) := target t.a ∧ ¬ target t.b ∧ target t.c ∧ ¬ target t.d
instance (t : Rule) : Decidable (labels t) := by unfold labels target; infer_instance
def Valid (t : Rule) := labels t ∧ ∀ s : Byte,
  t.rb.getLsbD s.val = hit t s (fun a => a.val/8) ∧
  t.cb.getLsbD s.val = hit t s (fun a => a.val%8)
instance (t : Rule) : Decidable (Valid t) := by unfold Valid; infer_instance

theorem excludes (r c : Byte) (hf : Fits r c) (t : Rule) (hv : Valid t)
    (hr : t.rb.getLsbD r.val = true) (hc : t.cb.getLsbD c.val = true) : False := by
  rw [(hv.2 r).1] at hr
  rw [(hv.2 c).2] at hc
  simp only [hit, Bool.and_eq_true] at hr hc
  obtain ⟨⟨u,v⟩,w⟩ := hr
  obtain ⟨⟨x,y⟩,z⟩ := hc
  obtain ⟨pa,nb,pc,nd⟩ := hv.1
  apply (SplitMonotoneFactor.four_row_criterion _ _ _).mp hf t.a t.b t.c t.d
  · exact ⟨pa,nb,mono_signal _ _ _ u,mono_signal _ _ _ x⟩
  · exact ⟨pc,nd,mono_signal _ _ _ v,mono_signal _ _ _ y⟩
  · exact ⟨mono_signal _ _ _ w,mono_signal _ _ _ z⟩

def union (r : Byte) : List Rule → BitVec 256
  | [] => 0
  | t::ts => (if t.rb.getLsbD r.val then t.cb else 0) ||| union r ts
theorem avoid (ts : List Rule) (v : ∀ t ∈ ts, Valid t) (r c : Byte) (hf : Fits r c) :
    (union r ts).getLsbD c.val = false := by
  induction ts with
  | nil => simp [union]
  | cons t ts ih =>
    have tail := ih (fun u h => v u (List.mem_cons_of_mem _ h))
    simp only [union, BitVec.getLsbD_or,tail,Bool.or_false]
    split
    · rename_i h
      cases he : t.cb.getLsbD c.val with
      | false => rfl
      | true => exact (excludes r c hf t (v t (by simp)) h he).elim
    · simp
end PlaneMask
#print axioms PlaneMask.excludes
#print axioms PlaneMask.avoid

import PEqualNP.Outside.L_meta_4101
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-! A singleton-positive AND that directly reads an input can be removed, even
when its output has many readers. More generally one can remove an AND with
a disjunctive operand if every generator of that operand activates the AND. -/
namespace PEqualNP.Research.SingletonAbsorption
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4101_aux

abbrev wire {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) := val C (List.ofFn x) w
def unit {n : ℕ} (s : Fin n) (i : Fin n) := decide (i=s)

theorem raw {n : ℕ} (C : Circuit) (s : Fin n) (x : Fin n → Bool) : wire C s.val x = x s := by
  rw [wire,val_input (n := n) (by simp) s.isLt,List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem propagates {n : ℕ} (C : Circuit) (hc : Monotone2 C) (w : ℕ) (s : Fin n) (x : Fin n → Bool)
    (bit : x s = true) (on : wire C w (unit s) = true) : wire C w x = true := by
  apply LowMergeProof.wires_mono C (fun g hg => (hc g hg).1) _ _ (by simp) ?_ w on
  intro i hi
  by_cases good : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using good),List.getElem_ofFn] at hi ⊢
    exact (of_decide_eq_true hi) ▸ bit
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

theorem delete_equal {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (r w : ℕ) (hr : r < C.gates.length) (hw : w < n+r)
    (same : ∀ x : Fin n → Bool, wire C (n+r) x = wire C w x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  refine ⟨bypass n C r w,?_,bypass_readsBack hw rb,?_,?_⟩
  · intro g hg
    obtain ⟨t,ht,op,len⟩ := bypass_mem g hg
    rw [op,len]; exact hc t ht
  · unfold Circuit.size
    rw [bypass_length]
    omega
  · funext x
    exact bypass_eval_eq (by simp) (fun k hk => (hc _ (gateAt_mem hk)).1) hr (Or.inl hw) (same x)

theorem absorb_union {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (r w : ℕ) (hr : r < C.gates.length) (op : (gateAt C r).op = .and)
    (read : w ∈ (gateAt C r).inputs) (S : Finset (Fin n))
    (disj : ∀ x : Fin n → Bool, wire C w x = true ↔ ∃ s ∈ S, x s = true)
    (covers : ∀ s ∈ S, wire C (n+r) (unit s) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  apply delete_equal C hc rb r w hr (rb r hr w read)
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro on; exact ((val_and (by simp) hr op).mp on w read).2
  · intro on
    obtain ⟨s,hs,xs⟩ := (disj x).mp on
    exact propagates C hc _ s x xs (covers s hs)

theorem absorb_raw {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (r : ℕ) (s t : Fin n) (hr : r < C.gates.length) (op : (gateAt C r).op = .and)
    (read : s.val ∈ (gateAt C r).inputs) (on : wire C (n+r) (unit t) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  have lit := ((val_and (by simp) hr op).mp on s.val read).2
  rw [show val C (List.ofFn (unit t)) s.val = unit t s from raw C s _] at lit
  obtain rfl : s = t := of_decide_eq_true lit
  exact absorb_union C hc rb r s.val hr op read {s} (by intro x; simp [raw]) (by simpa using on)

theorem normal_form {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
      ∀ r < D.size, (gateAt D r).op = .and → ∀ s : Fin n, s.val ∈ (gateAt D r).inputs →
        ∀ t : Fin n, wire D (n+r) (unit t) = false := by
  classical
  let P := fun k => ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ circuitFun n D = circuitFun n C ∧ D.size = k
  have ex : ∃ k, P k := ⟨C.size,C,hc,rb,rfl,rfl⟩
  obtain ⟨D,md,bd,ed,sz⟩ := Nat.find_spec ex
  refine ⟨D,md,bd,sz.trans_le (Nat.find_min' ex ⟨C,hc,rb,rfl,rfl⟩),ed,?_⟩
  intro r hr op s read t
  cases e : wire D (n+r) (unit t)
  · rfl
  · obtain ⟨K,mk,bk,sk,ek⟩ := absorb_raw D md bd r s t hr op read e
    have le := Nat.find_min' ex (show P K.size from ⟨K,mk,bk,ek.trans ed,rfl⟩)
    omega

theorem private_generator {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (least : ∀ D : Circuit, Monotone2 D → ReadsBack n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (r w : ℕ) (hr : r < C.size) (op : (gateAt C r).op = .and) (read : w ∈ (gateAt C r).inputs)
    (S : Finset (Fin n)) (disj : ∀ x, wire C w x = true ↔ ∃ s ∈ S, x s = true) :
    ∃ s ∈ S, wire C (n+r) (unit s) = false := by
  by_contra! all
  obtain ⟨D,md,bd,sz,eq⟩ := absorb_union C hc rb r w hr op read S disj (by simpa using all)
  have := least D md bd eq
  omega

open PEqualNP.EdgeOwnership in
theorem raw_operand_child :
let clean (n : ℕ) (C : Circuit) (j : ℕ) := ∀ i < j, (gateAt C i).op = GateOp.and →
        ∀ t : Fin n, gateVal n C i (fun k => decide (k = t)) = false
      let shape (C : Circuit) := ∀ j < C.size, (gateAt C j).op = GateOp.and →
        ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ≠ b
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j a b : ℕ),
        (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        Monotone2 C → ReadsBack (N+N) C → shape C →
        (∀ z, circuitFun (N+N) C z = true ↔
          ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        j < C.size → clean (N+N) C j → ¬ clean (N+N) C (j+1) →
        (gateAt C j).inputs = [a,b] → (a < N+N ∨ b < N+N) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧
          circuitFun (N+N) D = circuitFun (N+N) C ∧
          (D.size < C.size ∨ (D.size = C.size ∧ shape D ∧ clean (N+N) D (j+1))) := by
  dsimp only
  intro N I C j a b _ hc rb _ _ hj prev dirty args rawInput
  push Not at dirty
  obtain ⟨i,hi,op,t,on⟩ := dirty
  have ij : i = j := by
    by_contra h
    have := prev i (by omega) op t
    simp_all
  subst i
  obtain ⟨s,read⟩ : ∃ s : Fin (N+N), s.val ∈ (gateAt C j).inputs := by
    rcases rawInput with ha|hb
    · exact ⟨⟨a,ha⟩,args ▸ (by simp)⟩
    · exact ⟨⟨b,hb⟩,args ▸ (by simp)⟩
  obtain ⟨D,md,bd,size,eq⟩ := absorb_raw C hc rb j s t hj op read (by change gateVal (N+N) C j (fun k => decide (k = t)) = true; simpa using on)
  exact ⟨D,md,bd,eq,Or.inl (by omega)⟩

/-- No gate of a minimum circuit can compute a projection. A gate firing on a
singleton therefore also fires on an assignment omitting that input. -/
theorem no_mandatory_bit {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (least : ∀ D : Circuit, Monotone2 D → ReadsBack n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (r : ℕ) (hr : r < C.size) (s : Fin n) (on : wire C (n+r) (unit s) = true) (t : Fin n) :
    ∃ x : Fin n → Bool, x t = false ∧ wire C (n+r) x = true := by
  by_cases ts : t = s
  · subst t
    by_contra! necessary
    have eq (x : Fin n → Bool) : wire C (n+r) x = wire C s.val x := by
      rw [raw]
      cases h : x s
      · simpa using necessary x h
      · exact propagates C hc _ s x h on
    obtain ⟨D,md,bd,sz,ed⟩ := delete_equal C hc rb r s.val hr (by have := s.isLt; omega) eq
    have := least D md bd ed
    omega
  · exact ⟨unit s,by simp [unit,ts],on⟩

/-- In particular, both operands must still fire together after any prescribed
single raw input is turned off, even if both operands are computed gates. -/
theorem operands_escape {n : ℕ} (C : Circuit) (hc : Monotone2 C) (rb : ReadsBack n C)
    (least : ∀ D : Circuit, Monotone2 D → ReadsBack n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (r : ℕ) (hr : r < C.size) (op : (gateAt C r).op = .and) (s : Fin n)
    (on : wire C (n+r) (unit s) = true) (t : Fin n) :
    ∃ x : Fin n → Bool, x t = false ∧ ∀ w ∈ (gateAt C r).inputs, wire C w x = true := by
  obtain ⟨x,off,both⟩ := no_mandatory_bit C hc rb least r hr s on t
  exact ⟨x,off,fun w hw => ((val_and (by simp) hr op).mp both w hw).2⟩

end PEqualNP.Research.SingletonAbsorption

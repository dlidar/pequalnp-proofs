import PEqualNP.Research.L_meta_2584_budget

namespace PEqualNP.Research.ReadTwoStates
open PEqualNP.Research.ReadTwoBudget PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

def Up (f : State) : Prop := ∀ i j x y : Fin 3, i ≤ x → j ≤ y → f i j = true → f x y = true
def Legal (f : State) : Prop := Up f ∧ f 0 0 = false
def bit (m : Fin 512) (i j : Fin 3) : Bool := m.val.testBit (3*i.val+j.val)
def masks : List ℕ := [0, 256, 288, 292, 384, 416, 420, 432, 436, 438, 448, 480, 484, 496, 500, 502, 504, 508, 510]
instance (m : Fin 512) : Decidable (Legal (bit m)) := by unfold Legal Up; infer_instance

theorem exactly_nineteen : ∀ m : Fin 512, Legal (bit m) ↔ m.val ∈ masks := by decide +kernel
theorem distinct_nineteen : masks.length = 19 ∧ masks.Nodup := by decide +kernel

def code (f : State) : Fin 512 :=
  ⟨Nat.ofBits (fun k : Fin 9 => f (Fin.ofNat 3 (k.val/3)) (Fin.ofNat 3 (k.val%3))),
    Nat.ofBits_lt_two_pow _⟩

theorem decode (f : State) : bit (code f) = f := by
  funext i j
  unfold bit code
  rw [Nat.testBit_ofBits_lt _ _ (by have := i.isLt; have := j.isLt; omega)]
  fin_cases i <;> fin_cases j <;> rfl

def point : State := fun i _ => decide (1 ≤ i.val)
def lineSig : State := fun _ j => decide (1 ≤ j.val)
def spendP (f : State) : State := fun i j => if i.val = 0 then false else f ⟨i.val-1, by omega⟩ j
def spendL (f : State) : State := fun i j => if j.val = 0 then false else f i ⟨j.val-1, by omega⟩

theorem spend_point (f : State) (h : Up f) : mul f point = spendP f := by
  funext i j; apply Bool.eq_iff_iff.mpr
  simp only [mul,point,spendP,decide_eq_true_eq]
  by_cases hi : i.val = 0
  · simp [hi]
  · rw [if_neg hi]
    constructor
    · rintro ⟨u,v,x,y,h1,h2,hu,hx⟩
      exact h u v _ j (show u.val ≤ i.val-1 by omega) (show v.val ≤ j.val by omega) hu
    · intro hf; refine ⟨⟨i.val-1,by omega⟩,j,1,0,?_,by simp,hf,by decide⟩
      change i.val-1+1 ≤ i.val; omega

theorem spend_line (f : State) (h : Up f) : mul f lineSig = spendL f := by
  funext i j; apply Bool.eq_iff_iff.mpr
  simp only [mul,lineSig,spendL,decide_eq_true_eq]
  by_cases hj : j.val = 0
  · simp [hj]
  · rw [if_neg hj]
    constructor
    · rintro ⟨u,v,x,y,h1,h2,hu,hy⟩
      exact h u v i _ (show u.val ≤ i.val by omega) (show v.val ≤ j.val-1 by omega) hu
    · intro hf; refine ⟨i,⟨j.val-1,by omega⟩,0,1,by simp,?_,hf,by decide⟩
      change j.val-1+1 ≤ j.val; omega

def probe (f : State) (i j : Fin 3) : Bool :=
  ((spendP^[2-i.val]) ((spendL^[2-j.val]) f)) 2 2

theorem probe_eq (f : State) (i j : Fin 3) : probe f i j = f i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem distinguish {f g : State} (hne : f ≠ g) : ∃ i j, probe f i j ≠ probe g i j := by
  by_contra! eq
  apply hne
  funext i j
  simpa only [probe_eq] using eq i j

/-- A two-input AO2 program for every nonconstant upward budget predicate, plus the
empty predicate (three copies of the point). These programs can be used as prefixes. -/
def witness (m : ℕ) : Circuit := match m with
  | 0 => ⟨[⟨.and,[0,0]⟩, ⟨.and,[2,0]⟩], 3⟩
  | 256 => ⟨[⟨.and,[0,0]⟩, ⟨.and,[2,1]⟩, ⟨.and,[3,1]⟩], 4⟩
  | 288 => ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,1]⟩], 3⟩
  | 292 => ⟨[⟨.and,[1,1]⟩], 2⟩
  | 384 => ⟨[⟨.and,[0,0]⟩, ⟨.and,[2,1]⟩], 3⟩
  | 416 => ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,1]⟩, ⟨.and,[0,0]⟩, ⟨.and,[4,1]⟩, ⟨.or,[3,5]⟩], 6⟩
  | 420 => ⟨[⟨.and,[1,1]⟩, ⟨.and,[0,0]⟩, ⟨.and,[3,1]⟩, ⟨.or,[2,4]⟩], 5⟩
  | 432 => ⟨[⟨.and,[0,1]⟩], 2⟩
  | 436 => ⟨[⟨.and,[1,1]⟩, ⟨.and,[0,1]⟩, ⟨.or,[2,3]⟩], 4⟩
  | 438 => ⟨[], 1⟩
  | 448 => ⟨[⟨.and,[0,0]⟩], 2⟩
  | 480 => ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,1]⟩, ⟨.and,[0,0]⟩, ⟨.or,[3,4]⟩], 5⟩
  | 484 => ⟨[⟨.and,[1,1]⟩, ⟨.and,[0,0]⟩, ⟨.or,[2,3]⟩], 4⟩
  | 496 => ⟨[⟨.and,[0,1]⟩, ⟨.and,[0,0]⟩, ⟨.or,[2,3]⟩], 4⟩
  | 500 => ⟨[⟨.and,[1,1]⟩, ⟨.and,[0,1]⟩, ⟨.and,[0,0]⟩, ⟨.or,[2,3]⟩, ⟨.or,[5,4]⟩], 6⟩
  | 502 => ⟨[⟨.and,[0,0]⟩, ⟨.or,[1,2]⟩], 3⟩
  | 504 => ⟨[], 0⟩
  | 508 => ⟨[⟨.and,[1,1]⟩, ⟨.or,[2,0]⟩], 3⟩
  | 510 => ⟨[⟨.or,[1,0]⟩], 2⟩
  | _ => ⟨[],0⟩

theorem realize : ∀ m ∈ masks, IsAO2 2 (witness m) ∧
    ∀ i j : Fin 3, encode ((readVectors (witness m) 2 [0,1] 2).getD (witness m).output []) i j =
      m.testBit (3*i.val+j.val) := by decide +kernel

#print axioms realize
#print axioms distinguish
theorem zero_legal : Legal zero := by simp [Legal,Up,zero]
theorem legal_add {a b : State} (ha : Legal a) (hb : Legal b) : Legal (add a b) := by
  constructor
  · intro i j x y hx hy h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (ha.1 i j x y hx hy h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (hb.1 i j x y hx hy h))
  · simp [add,ha.2,hb.2]

theorem legal_mul {a b : State} (ha : Legal a) (_hb : Legal b) : Legal (mul a b) := by
  constructor
  · intro i j x y hx hy h
    obtain ⟨s,t,u,v,h1,h2,hs,ht⟩ := of_decide_eq_true h
    exact decide_eq_true ⟨s,t,u,v,h1.trans hx,h2.trans hy,hs,ht⟩
  · apply decide_eq_false
    rintro ⟨s,t,u,v,h1,h2,hs,_⟩
    change s.val+u.val ≤ 0 at h1
    change t.val+v.val ≤ 0 at h2
    have s0 : s = 0 := Fin.ext (by change s.val = 0; omega)
    have t0 : t = 0 := Fin.ext (by change t.val = 0; omega)
    simp [s0,t0,ha.2] at hs

theorem leaf_legal (a b i : ℕ) : Legal (encode (leafVectors [a,b] 2 i)) := by
  refine ⟨mono_encode _,?_⟩
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [leafVectors,encode,fits,List.getD]

theorem fast_legal (C : Circuit) (n a b o : ℕ) :
    Legal ((fastWires C n a b).getD o zero) := by
  have lookup (W : List State) (h : ∀ f ∈ W, Legal f) (i : ℕ) : Legal (W.getD i zero) := by
    by_cases hb : i < W.length
    · rw [List.getD_eq_getElem _ _ hb]; exact h _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; exact zero_legal
  have fold (gs : List Gate) (W : List State) (h : ∀ f ∈ W, Legal f) :
      ∀ f ∈ gs.foldl (fun w g => w ++ [fastStep w g]) W, Legal f := by
    induction gs generalizing W with
    | nil => exact h
    | cons g gs ih =>
      apply ih
      intro f hf
      simp only [List.mem_append,List.mem_singleton] at hf
      rcases hf with hf | rfl
      · exact h _ hf
      · cases hg : g.op <;> simp only [fastStep,hg] <;>
          first | apply legal_mul <;> apply lookup _ h
                | apply legal_add <;> apply lookup _ h
                | exact zero_legal
  apply lookup _ _ o
  apply fold
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact leaf_legal _ _ _

theorem reachable_code (C : Circuit) (n a b o : ℕ) :
    (code ((fastWires C n a b).getD o zero)).val ∈ masks := by
  apply (exactly_nineteen _).mp
  rw [decode]; exact fast_legal _ _ _ _ _

#print axioms reachable_code
end PEqualNP.Research.ReadTwoStates

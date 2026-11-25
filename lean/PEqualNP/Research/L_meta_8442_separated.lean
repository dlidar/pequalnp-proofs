import PEqualNP.Research.L_meta_8442_bridge

namespace PEqualNP.Research.BridgeTriangles

def truth (i j : Fin 16) : Bool :=
  graph (i.val.testBit 0) (i.val.testBit 1) (i.val.testBit 2) (i.val.testBit 3)
    (j.val.testBit 3) (j.val.testBit 0) (j.val.testBit 1) (j.val.testBit 2)

theorem truth_comm : ∀ i j, truth i j = truth j i := by decide +kernel

-- The opposite side can be read in full, with an arbitrary joint decoder.
theorem left_encoding_cost {n : Nat} {s : List Word} {x y : Word}
    (run : Run n initial s) (hx : x ∈ s) (hy : y ∈ s)
    (D : Bool → Bool → Fin 16 → Bool)
    (h : ∀ i j : Fin 16, D (x.getLsbD i.val) (y.getLsbD i.val) j = truth i j) : 5 ≤ n := by
  apply five_local_gates run hx hy
  apply separates_of_probes _ _ (fun a b => D a b 0) (fun a b => D a b 8)
  · intro i
    exact (probe_masks i).1.symm.trans (h i 0).symm
  · intro i
    exact (probe_masks i).2.symm.trans (h i 8).symm

abbrev Matrix := Fin 3 → Fin 3 → Bool
def Pure (x : Matrix) := ∃ l p, x = feature l p
abbrev Signal (α : Type) := α → α → Bool
def join {α : Type} (d : Bool → Bool → Bool) (a b : Signal α) : Signal α := fun i j => d (a i j) (b i j)

theorem two_mixed_obstruction {a b c d : Matrix} (ha : Pure a) (hb : Pure b)
    (f g : Bool → Bool → Bool)
    (hc : Pure c ∨ c = join f a b) (hd : Pure d ∨ d = join f a b)
    (h : join g c d = matrix) : False := by
  obtain ⟨la,pa,rfl⟩ := ha
  obtain ⟨lb,pb,rfl⟩ := hb
  rcases hc with ⟨lc,pc,rfl⟩|rfl <;> rcases hd with ⟨ld,pd,rfl⟩|rfl
  · exact three_features lc ld ld pc pd pd (fun x y _ => g x y) (congrFun₂ h)
  · exact three_features lc la lb pc pa pb (fun x y z => g x (f y z)) (congrFun₂ h)
  · exact three_features la lb ld pa pb pd (fun x y z => g (f x y) z) (congrFun₂ h)
  · exact three_features la lb lb pa pb pb (fun x y _ => g (f x y) (f x y)) (congrFun₂ h)

-- The mixed processor may use arbitrary binary gates, including projections.
inductive Processor {α : Type} : Nat → (Signal α → Prop) → Signal α → Prop
  | out {k S m} : S m → Processor k S m
  | add {k S m a b} (f : Bool → Bool → Bool) : S a → S b →
      Processor k (fun z => S z ∨ z = join f a b) m → Processor (k+1) S m

private theorem processor_extend {k n : Nat} {S : Matrix → Prop} {m : Matrix}
    (h : Processor k S m) (hn : k ≤ n) : Processor n S m := by
  induction h generalizing n with
  | out hm => exact .out hm
  | add f ha hb _ ih =>
    cases n with
    | zero => omega
    | succ n => exact .add f ha hb (ih (by omega))

private theorem one_gate_obstruction {a b : Matrix} (ha : Pure a) (hb : Pure b)
    (f : Bool → Bool → Bool) (h : join f a b = matrix) : False :=
  two_mixed_obstruction ha hb f f (Or.inl ha) (Or.inl hb) h

theorem three_mixed_gates {k : Nat} (h : Processor k Pure matrix) : 3 ≤ k := by
  by_contra! hk
  have run := processor_extend h (show k ≤ 2 by omega)
  have hp : ¬Pure matrix := fun hm => one_gate_obstruction hm hm (fun x _ => x) rfl
  cases run with
  | out h => exact hp h
  | add f ha hb run =>
    cases run with
    | out h =>
      rcases h with h|h
      · exact hp h
      · exact one_gate_obstruction ha hb f h.symm
    | add g hc hd run =>
      cases run with
      | out h =>
        rcases h with (h|h)|h
        · exact hp h
        · exact one_gate_obstruction ha hb f h.symm
        · exact two_mixed_obstruction ha hb f g hc hd h.symm

theorem separated_bound {n m k : Nat} {s t : List Word} {x y v w : Word}
    (l : Run n initial s) (r : Run m initial t) (hx : x ∈ s) (hy : y ∈ s)
    (hv : v ∈ t) (hw : w ∈ t) (D : Bool → Bool → Bool → Bool → Bool)
    (correct : ∀ i j : Fin 16, D (x.getLsbD i.val) (y.getLsbD i.val)
      (v.getLsbD j.val) (w.getLsbD j.val) = truth i j)
    (mixed : Processor k Pure matrix) : 13 ≤ n + m + k := by
  have h₁ := left_encoding_cost l hx hy
    (fun a b j => D a b (v.getLsbD j.val) (w.getLsbD j.val)) correct
  have h₂ := left_encoding_cost r hv hw
    (fun a b i => D (x.getLsbD i.val) (y.getLsbD i.val) a b)
    (fun j i => (correct i j).trans (truth_comm i j))
  have h₃ := three_mixed_gates mixed
  omega

def ports (x y v w : Word) (m : Signal (Fin 16)) : Prop :=
  m = (fun i _ => x.getLsbD i.val) ∨ m = (fun i _ => y.getLsbD i.val) ∨
  m = (fun _ j => v.getLsbD j.val) ∨ m = (fun _ j => w.getLsbD j.val)

theorem processor_invariant {α : Type} {k : Nat} {S P : Signal α → Prop} {m : Signal α}
    (h : Processor k S m) (initially : ∀ z, S z → P z)
    (closed : ∀ f a b, P a → P b → P (join f a b)) : P m := by
  induction h with
  | out hm => exact initially _ hm
  | add f ha hb _ ih =>
    apply ih
    intro z hz
    rcases hz with hz|rfl
    · exact initially _ hz
    · exact closed _ _ _ (initially _ ha) (initially _ hb)

theorem processor_reindex {α β : Type} {k : Nat} {S : Signal α → Prop}
    {T : Signal β → Prop} {m : Signal α} (sampleAt : β → α) (h : Processor k S m)
    (images : ∀ a, S a → T (fun i j => a (sampleAt i) (sampleAt j))) :
    Processor k T (fun i j => m (sampleAt i) (sampleAt j)) := by
  induction h generalizing T with
  | out hm => exact .out (images _ hm)
  | add f ha hb _ ih =>
    apply Processor.add f (images _ ha) (images _ hb)
    apply ih
    intro z hz
    rcases hz with hz|rfl
    · exact Or.inl (images _ hz)
    · exact Or.inr rfl

def row (i : Fin 3) : Fin 16 := if i = 0 then 0 else if i = 1 then 8 else 3
theorem matrix_on_rows : (fun i j => truth (row i) (row j)) = matrix := by decide +kernel

theorem bridge_bound {n m k : Nat} {s t : List Word} {x y v w : Word}
    (l : Run n initial s) (r : Run m initial t) (hx : x ∈ s) (hy : y ∈ s)
    (hv : v ∈ t) (hw : w ∈ t) (mixed : Processor k (ports x y v w) truth) :
    13 ≤ n + m + k := by
  let P (z : Signal (Fin 16)) := ∃ D : Bool → Bool → Bool → Bool → Bool,
    ∀ i j : Fin 16, D (x.getLsbD i.val) (y.getLsbD i.val) (v.getLsbD j.val) (w.getLsbD j.val) = z i j
  have hd : P truth := by
    apply processor_invariant mixed
    · intro z hz
      rcases hz with rfl|rfl|rfl|rfl
      · exact ⟨fun a _ _ _ => a,fun _ _ => rfl⟩
      · exact ⟨fun _ b _ _ => b,fun _ _ => rfl⟩
      · exact ⟨fun _ _ c _ => c,fun _ _ => rfl⟩
      · exact ⟨fun _ _ _ d => d,fun _ _ => rfl⟩
    · rintro f a b ⟨D,hd⟩ ⟨E,he⟩
      exact ⟨fun w x y z => f (D w x y z) (E w x y z),fun i j => congrArg₂ f (hd i j) (he i j)⟩
  obtain ⟨D,hd⟩ := hd
  apply separated_bound l r hx hy hv hw D hd
  rw [← matrix_on_rows]
  apply processor_reindex row mixed
  intro z hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact ⟨true,fun i => x.getLsbD (row i).val,rfl⟩
  · exact ⟨true,fun i => y.getLsbD (row i).val,rfl⟩
  · exact ⟨false,fun i => v.getLsbD (row i).val,rfl⟩
  · exact ⟨false,fun i => w.getLsbD (row i).val,rfl⟩

theorem input_masks : ∀ i : Fin 4, ∀ r : Fin 16,
    ((initial[i.val]?.getD 0).getLsbD r.val) = r.val.testBit i.val := by decide +kernel

def fiveWires : List Word := 60136 :: 49344 :: 43688 :: 65532 :: 64764 :: initial

theorem five_encoder : Run 5 initial fiveWires := by
  apply Run.add (z := 64764) (by decide +kernel)
  apply Run.add (z := 65532) (by decide +kernel)
  apply Run.add (z := 43688) (by decide +kernel)
  apply Run.add (z := 49344) (by decide +kernel)
  apply Run.add (z := 60136) (by decide +kernel)
  exact Run.done

theorem three_decoder :
    Processor 3 (ports leftHit 65280 leftHit 65280) truth := by
  let a : Signal (Fin 16) := fun i _ => leftHit.getLsbD i.val
  let b : Signal (Fin 16) := fun _ j => leftHit.getLsbD j.val
  let u : Signal (Fin 16) := fun i _ => (65280 : Word).getLsbD i.val
  let v : Signal (Fin 16) := fun _ j => (65280 : Word).getLsbD j.val
  have ha : ports leftHit 65280 leftHit 65280 a := Or.inl rfl
  have hb : ports leftHit 65280 leftHit 65280 b := Or.inr (Or.inr (Or.inl rfl))
  have hu : ports leftHit 65280 leftHit 65280 u := Or.inr (Or.inl rfl)
  have hv : ports leftHit 65280 leftHit 65280 v := Or.inr (Or.inr (Or.inr rfl))
  apply Processor.add Bool.and hu hv
  apply Processor.add Bool.or (Or.inl ha) (Or.inl hb)
  apply Processor.add Bool.or (Or.inr (show join Bool.or a b = _ from rfl))
    (Or.inl (Or.inr (show join Bool.and u v = _ from rfl)))
  exact Processor.out (Or.inr (by decide +kernel))

theorem sharp_budget :
    (∃ s : List Word, Run 5 initial s ∧ leftHit ∈ s ∧ (65280 : Word) ∈ s) ∧
    Processor 3 (ports leftHit 65280 leftHit 65280) truth :=
  ⟨⟨fiveWires,five_encoder,by decide +kernel,by decide +kernel⟩,three_decoder⟩


end PEqualNP.Research.BridgeTriangles

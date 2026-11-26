import PEqualNP.Defs.MetaComplexityLgpMono
namespace PEqualNP.Research.SelectorBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev W := List Bool
def read (w : W) (i : ℕ) := w.getD i false
def val (g : Gate) (w : W) := g.op.eval (g.inputs.map (read w))
def sensitive (b : Bool) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .or, [_,_] => b
  | .and, [_,_] => !b
  | _,_ => false
def total (b : Bool) (gs : List Gate) := (gs.filter (sensitive b)).length
def code (b : Bool) : List Gate → W → ℕ
  | [],_ => 0
  | g::gs,w =>
    let t := code b gs (w ++ [val g w])
    if sensitive b g then 2*t + (read w (g.inputs.headD 0)).toNat else t
theorem code_lt (b : Bool) (gs : List Gate) (w : W) : code b gs w < 2^(total b gs) := by
  induction gs generalizing w with
  | nil => simp [code,total]
  | cons g gs ih =>
    have h := ih (w++[val g w])
    cases hs : sensitive b g with
    | false => simpa only [code,hs,Bool.false_eq_true,ite_false,total,List.filter_cons_of_neg (by simp [hs] : ¬ sensitive b g = true)] using h
    | true =>
      have u := Bool.toNat_le (read w (g.inputs.headD 0))
      simp only [code,hs,ite_true,total,List.filter_cons_of_pos hs,List.length_cons,pow_succ] at *
      omega
def agree (b : Bool) (x y z : W) := ∀ i, read x i = b → read y i = b → read z i = b
theorem append_agree {b a d e : Bool} {x y z : W}
    (l : x.length = y.length) (m : x.length = z.length) (h : agree b x y z)
    (v : a = b → d = b → e = b) : agree b (x++[a]) (y++[d]) (z++[e]) := by
  intro i
  by_cases hi : i < x.length
  · simpa only [read,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (l ▸ hi),List.getD_append _ _ _ _ (m ▸ hi)] using h i
  · unfold read
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← l,← m]
    cases i - x.length with
    | zero => simpa using v
    | succ n => simp
theorem gate_agree (b : Bool) (g : Gate) (x y z : W) (h : agree b x y z)
    (legal : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2)
    (same : sensitive b g = true → read x (g.inputs.headD 0) = read y (g.inputs.headD 0)) :
    val g x = b → val g y = b → val g z = b := by
  obtain ⟨op,ins⟩ := g
  change op = .and ∨ op = .or at legal
  change ins.length ≤ 2 at arity
  rcases legal with rfl|rfl <;> cases ins with
  | nil => simp [val]
  | cons i tail =>
    cases tail with
    | nil => simpa [val,GateOp.eval] using h i
    | cons j tail =>
      cases tail with
      | cons a rest => simp at arity
      | nil =>
        have hi := h i
        have hj := h j
        cases b <;> simp only [sensitive,val,GateOp.eval,List.map_cons,List.map_nil] at * <;>
          cases ex : read x i <;> cases ey : read y i <;> cases ez : read z i <;>
          simp_all
def run (gs : List Gate) (w : W) := gs.foldl (fun z g => z ++ [val g z]) w
theorem run_agree (b : Bool) (gs : List Gate) (x y z : W)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (l : x.length=y.length) (m : x.length=z.length) (h : agree b x y z)
    (sig : code b gs x = code b gs y) : agree b (run gs x) (run gs y) (run gs z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    have hg := legal g (by simp)
    have htail := fun t (ht : t ∈ gs) => legal t (by simp [ht])
    apply ih _ _ _ htail (by simp [l]) (by simp [m])
    · apply append_agree l m h (gate_agree b g x y z h hg.1 hg.2 _)
      intro hs
      simp only [code,hs,ite_true] at sig
      cases ex : read x (g.inputs.headD 0) <;> cases ey : read y (g.inputs.headD 0) <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
    · cases hs : sensitive b g <;> simp only [code,hs,ite_true,Bool.false_eq_true,ite_false] at sig
      · exact sig
      · cases ex : read x (g.inputs.headD 0) <;> cases ey : read y (g.inputs.headD 0) <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
theorem circuit_packing {k : ℕ} (b : Bool) (C : Circuit) (mono : Monotone2 C)
    (r : Fin k → W) (outputs : ∀ i, C.eval (r i) = b)
    (sep : ∀ i j, i < j → ∃ z, (r i).length=(r j).length ∧ (r i).length=z.length ∧
      agree b (r i) (r j) z ∧ C.eval z ≠ b) :
    k ≤ 2^(total b C.gates) := by
  let f : Fin k → Fin (2^(total b C.gates)) := fun i => ⟨_,code_lt b C.gates (r i)⟩
  have ord : ∀ i j, i < j → f i ≠ f j := by
    intro i j lt eq
    obtain ⟨z,l,m,h,hz⟩ := sep i j lt
    exact hz (run_agree b C.gates _ _ _ (fun g hg => mono g hg) l m h (congrArg Fin.val eq) C.output (outputs i) (outputs j))
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i j with hl|he|hr
    · exact (ord i j hl eq).elim
    · exact he
    · exact (ord j i hr eq.symm).elim
  simpa using Fintype.card_le_of_injective f inj

theorem packing_child : ∀ (k : ℕ) (b : Bool) (C : Circuit), Monotone2 C → ∀ (r : Fin k → List Bool),
      (∀ i, C.eval (r i) = b) → (∀ i j, i < j → ∃ z : List Bool, (r i).length = (r j).length ∧ (r i).length = z.length ∧ (∀ a : ℕ, (r i).getD a false = b → (r j).getD a false = b → z.getD a false = b) ∧ C.eval z ≠ b) → k ≤ 2^(C.gates.filter (fun g => (g.inputs.length == 2) && (g.op.eval [true,false] == b))).length := by
  intro k b C mono r v pair
  have bound := circuit_packing b C mono r v pair
  convert bound using 3
  unfold total
  congr 1
  apply List.filter_congr
  intro g hg
  obtain ⟨op,ar⟩ := mono g hg
  change g.op = .and ∨ g.op = .or at op
  rcases op with h|h <;> cases b <;>
    cases eq : g.inputs with
    | nil => simp [sensitive,h,eq,GateOp.eval]
    | cons i tl =>
      cases tl with
      | nil => simp [sensitive,h,eq,GateOp.eval]
      | cons j rest =>
        cases rest with
        | nil => simp [sensitive,h,eq,GateOp.eval]
        | cons z zs => simp [eq] at ar
end PEqualNP.Research.SelectorBound

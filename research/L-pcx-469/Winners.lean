import CompilePrice
namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k H I W U : ℕ}
def winner (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a : Fin (k+1)) (y : Packet (H*I)) : Prop :=
  ∀ a' : Fin (k+1), totalPrice k f m e a.val (rows W y) ≤ totalPrice k f m e a'.val (rows W y)

theorem score_le_gate (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I+1≤U)
    (hM : Fintype.card (Model b k) ≤ U) (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a a' : ℕ) :
    gateP (packet (H*I) W) U 32 (fun y => totalPrice k f m e a (rows W y) ≤ totalPrice k f m e a' (rows W y)) := by
  let T := fun (a : ℕ) (y : Packet (H*I)) => totalPrice k f m e a (rows W y)
  let J := Fin (H*I+1)
  let good := fun (j : J) (y : Packet (H*I)) => ¬ (j.val ≤ T a y ∧ ¬ j.val ≤ T a' y)
  have cut (a j : ℕ) : gateP (packet (H*I) W) U 22 (fun y => j ≤ T a y) :=
    total_cut hU hW hI (by omega) hM f m e a j
  have hg (j : J) : gateP (packet (H*I) W) U 28 (good j) :=
    gate_not _ hU (gate_and _ hU (gate_lift _ (by omega : 1≤U) (by decide : 22≤23) (cut a j.val)) (gate_not _ hU (cut a' j.val)))
  apply gate_congr _ (gate_all _ hU (show Fintype.card J ≤ U by simpa [J] using hd) good hg)
  intro y
  change (∀ j : J, ¬ (j.val ≤ T a y ∧ ¬ j.val ≤ T a' y)) ↔ T a y ≤ T a' y
  constructor
  · intro hh
    have ht := price_total_cap (k:=k) f m e a (rows W y)
    let j : J := ⟨T a y,by dsimp [T];omega⟩
    have hj := hh j
    change ¬(T a y ≤ T a y ∧ ¬ T a y ≤ T a' y) at hj
    omega
  · intro h j;omega

theorem winner_gate (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I+1≤U)
    (hM : Fintype.card (Model b k) ≤ U) (hk : k+1≤U) (f : Fin H → Label t b)
    (m : Fin I → Mask b) (e : Pair t) (a : Fin (k+1)) :
    gateP (packet (H*I) W) U 36 (winner (W:=W) f m e a) := by
  exact gate_all _ hU (by simpa using hk) _ (fun a' : Fin (k+1) => score_le_gate hU hW hI hd hM f m e a.val a'.val)

theorem realizes {J : Type} [Fintype J] {X : Type} {n r : ℕ} (E : Encoding X n) (U : ℕ)
    (F : J → X → Bool) (hF : ∀ j, level E U r (F j)) (hj : Fintype.card J ≤ U) :
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (out : J → Fin (n+g.size)),
    g.size ≤ U^(r+1) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n g ∧
    (∀ gate ∈ g.gates, allowed gate) ∧ ∀ j x, (g.wires (E.base x)).getD (out j).val false = F j x := by
  classical
  let bij := Fintype.equivFin J
  let fs := fun (i : Fin (Fintype.card J)) => F (bij.symm i)
  obtain ⟨p,o,hp,hl,ho,he⟩ := indexed (B:=U^r) fs (fun i => hF (bij.symm i)) n le_rfl
  have hlegal := circuit_legal hp
  refine ⟨⟨p,0⟩,fun j => ⟨o (bij j),ho _⟩,?_,hlegal.1,hlegal.2,?_⟩
  · change p.length ≤ _
    rw [pow_succ,Nat.mul_comm (U^r)];exact hl.trans (Nat.mul_le_mul_right _ hj)
  · intro j x
    change (run p (E.base x)).getD (o (bij j)) false = F j x
    simpa [fs] using he x (E.base x) (E.length x) (by rfl) (bij j)
end SpinCircuit

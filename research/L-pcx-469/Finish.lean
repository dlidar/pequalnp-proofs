import Pack
import Sizes

namespace SpinSolution
open SpinCircuit SpinHash SpinMass Finset

theorem assembled : ∃ C A : ℕ, 0 < C ∧ ∀ t k s : ℕ, 2 ≤ t → 0 < k → 3 ≤ s →
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let E := Fin 3 × T
  let Mask := T → Fin 3
  let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
  let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
  let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs := fun (g : Option Pair) (p : Mask) =>
    ∑ x : V → Bool, if (∀ i : T, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2*t then
      ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0

  let Model := Fin k → Option Pair
  let read := fun (G : Model) (p : Mask) => ∏ l, obs (G l) p
  let W := k*(2*t+2)+1
  ∃ (d : ℕ) (batch : Fin d → Mask) (g : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Pair → Fin (k+1) → Fin (2+d*(W+1)+g.size)),
    0 < d ∧ d ≤ C*(k+1)^2*s^3*(1+Nat.log 2 ((k+1)*s))*(1+Nat.log 2 t) ∧
    g.size ≤ (t+2)^A*(k+s+2)^(A*(k+1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+d*(W+1)) g ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (G : Model), (∀ i, read G (batch i) < 2^W) ∧
      ∀ (y : Fin d → Option ℕ),
        let lost := (Finset.univ.filter (fun i => y i = none)).card
        let err := (Finset.univ.filter (fun i => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card
        9*s*(2*err+lost) < (4*s-9)*d →
        let bits := (List.ofFn (fun i : Fin d => (y i).isSome ::
          List.ofFn (fun j : Fin W => ((y i).getD 0).testBit j.val))).flatten
        ∀ (e : Pair) (m : Fin (k+1)), (g.wires ([false,true] ++ bits)).getD (out e m).val false =
          decide ((Finset.univ.filter (fun l => G l = some e)).card = m.val) := by
  classical
  refine ⟨67584,1184,by decide,?_⟩
  intro t k s ht hk hs
  dsimp only
  let H := outer t k s
  let I := inner k s
  let W := fullW k t
  let U := cap t k s
  obtain ⟨f,m,win⟩ := local_design t k s hs
  obtain ⟨hu,hw,hi,hd,hM,hk',hj⟩ := parameter_bounds t k s ht hk hs
  let Q := Pair t × Fin (k+1)
  let F := fun (z : Q) (y : Packet (H*I)) => decide (winner (W:=W) f m z.1 z.2 y)
  have hf (z : Q) : level (packet (H*I) W) U 36 (F z) := by
    apply to_bool (packet (H*I) W) (winner_gate hu hw hi hd hM hk' f m z.1 z.2)
    intro y; exact decide_eq_true_iff
  obtain ⟨g,o,hsize,hback,hops,heval⟩ := realizes (packet (H*I) W) U F hf hj
  have hH : 0 < H := by dsimp [H,outer,colors,outerL];positivity
  have hI : 0 < I := by dsimp [I,SpinHash.inner,slotBits];positivity
  refine ⟨H*I,batch f m,g,fun e a => o (e,a),Nat.mul_pos hH hI,query_budget t k s (by omega),?_,hback,hops,?_⟩
  · exact hsize.trans_eq (final_size ..)
  · intro G
    refine ⟨fun i => reading_bound G _,?_⟩
    intro y
    dsimp only
    intro hr e a
    have hbad := error_rows f m G y
    have hlost := lost_rows W y
    have hrob : 9*s*(2*totalErrors f m G (rows W y)+totalLost (rows W y)) < (4*s-9)*(H*I) := by
      apply lt_of_le_of_lt _ hr
      apply Nat.mul_le_mul_left
      rw [hlost]
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left 2 hbad
    have hwin := win G e (rows W y) hrob
    have hsem := heval (e,a) y
    change (g.wires ((packet (H*I) W).base y)).getD (o (e,a)).val false = decide (winner (W:=W) f m e a y) at hsem
    rw [show (packet (H*I) W).base y = _ from packet_layout _ _ y] at hsem
    change (g.wires _).getD (o (e,a)).val false = decide (mult G e = a.val)
    apply hsem.trans
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using winning_value f m G e W y hwin a

end SpinSolution

import LogicGates
namespace SpinCircuit
open Finset
abbrev Packet (d : ℕ) := Fin d → Option ℕ
def wireBit {W : ℕ} (v : Option ℕ) (j : Fin (W+1)) : Bool :=
  if j.val=0 then v.isSome else (v.getD 0).testBit (j.val-1)
def packetBits (d W : ℕ) (v : Packet d) := [false,true] ++ List.ofFn (fun i : Fin (d*(W+1)) =>
  let ij := finProdFinEquiv.symm i
  wireBit (v ij.1) ij.2)
def packet (d W : ℕ) : Encoding (Packet d) (2+d*(W+1)) where
  base := packetBits d W
  length v := by simp [packetBits];omega
  enough := by omega
  zero v := rfl
  one v := rfl

theorem packet_layout (d W : ℕ) (v : Packet d) : packetBits d W v = [false,true] ++
    (List.ofFn (fun i : Fin d => (v i).isSome :: List.ofFn (fun j : Fin W => ((v i).getD 0).testBit j.val))).flatten := by
  unfold packetBits
  rw [List.ofFn_mul]
  congr 2
  apply congrArg List.ofFn
  funext i
  have hh (j : Fin (W+1)) : (⟨i.val*(W+1)+j.val,by have hj:=j.isLt;have h:=Nat.mul_le_mul_right (W+1) i.isLt;rw [Nat.succ_mul] at h;omega⟩ : Fin (d*(W+1))) = finProdFinEquiv (i,j) := by
    apply Fin.ext; simp [Nat.add_comm,Nat.mul_comm]
  simp only [hh,Equiv.symm_apply_apply]
  rw [List.ofFn_succ]
  congr 1

theorem bit_gate {d W U r : ℕ} (i : Fin d) (j : Fin (W+1)) :
    level (packet d W) U r (fun y => wireBit (y i) j) := by
  let loc := finProdFinEquiv (i,j)
  let ix : Fin (2+d*(W+1)) := ⟨2+loc.val,by have h:=loc.isLt;omega⟩
  have h := read_input (packet d W).base (packet d W).length ix
  have hh (y : Packet d) : ((packet d W).base y).getD ix false = wireBit (y i) j := by
    change ([false,true] ++ _).getD (2+loc.val) false = _
    rw [Nat.add_comm 2]
    change (List.ofFn (fun u : Fin (d*(W+1)) => wireBit (y (finProdFinEquiv.symm u).1) (finProdFinEquiv.symm u).2)).getD loc.val false = _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos loc.isLt, Option.getD_some]
    exact congrArg (fun ij : Fin d × Fin (W+1) => wireBit (y ij.1) ij.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simpa only [level,hh] using weaken h (Nat.zero_le (U^r))

def clip (W : ℕ) (v : Option ℕ) := v.map (· % 2^W)
theorem bit_match (a v W : ℕ) (ha : a<2^W) :
    v%2^W = a ↔ ∀ j : Fin W, v.testBit j.val = a.testBit j.val := by
  have h : a%2^W = a := Nat.mod_eq_of_lt ha
  constructor
  · intro he j
    have hh := congrArg (fun z : ℕ => z.testBit j.val) he
    simpa [Nat.testBit_mod_two_pow,j.isLt] using hh
  · intro hb;rw [←h];apply Nat.eq_of_testBit_eq;intro j
    by_cases hj : j<W
    · simp [Nat.testBit_mod_two_pow,hj,hb ⟨j,hj⟩]
    · simp [Nat.testBit_mod_two_pow,hj]

theorem present_gate {d W U r : ℕ} (i : Fin d) :
    gateP (packet d W) U r (fun y => y i ≠ none) := by
  classical
  have h := bit_gate (W := W) (U := U) (r := r) i 0
  have hh (y : Packet d) : wireBit (y i) (0 : Fin (W+1)) = decide (y i ≠ none) := by
    cases hi : y i <;> simp [wireBit]
  apply of_bool (packet d W) h
  intro y;rw [hh];simp

theorem matches_constant {d W U : ℕ} (hU : 4≤U) (hW : W≤U) (i : Fin d) (a : ℕ) (ha : a<2^W) :
    gateP (packet d W) U 5 (fun y => (y i).getD 0 % 2^W = a) := by
  classical
  let P := fun (j : Fin W) (y : Packet d) => ((y i).getD 0).testBit j.val = a.testBit j.val
  have hp (j : Fin W) : gateP (packet d W) U 1 (P j) := by
    have hr := bit_gate (W:=W) (U:=U) (r:=0) i j.succ
    have hb (y : Packet d) : wireBit (y i) j.succ = ((y i).getD 0).testBit j.val := by simp [wireBit]
    simp only [hb] at hr
    cases hj : a.testBit j.val with
    | true =>
      have he (y : Packet d) : decide (P j y) = ((y i).getD 0).testBit j.val := by simp [P,hj]
      apply of_bool (packet d W) (lift_level (packet d W) (by omega : 1≤U) (by decide : 0≤1) hr)
      intro y;simp [P,hj]
    | false =>
      have he (y : Packet d) : decide (P j y) = !((y i).getD 0).testBit j.val := by simp [P,hj]
      apply of_bool (packet d W) (level_not (packet d W) hU hr)
      intro y;simp [P,hj]
  exact gate_congr (packet d W) (gate_all (packet d W) hU (by simpa using hW) P hp)
    (fun y => (bit_match a ((y i).getD 0) W ha).symm)

end SpinCircuit

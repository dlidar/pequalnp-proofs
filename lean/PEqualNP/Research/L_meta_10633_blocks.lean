import PEqualNP.Research.L_meta_10633_repairs
import PEqualNP.Research.L_meta_11718_circuits

namespace PEqualNP.Research.DenseReplacementBlocks
open PEqualNP.CircuitLowerBounds PEqualNP.Research.DenseRepairs
open PEqualNP.Research.InverterCircuit

private def binary (op : GateOp) (a b : Circuit) (start : Nat) : Circuit :=
  ⟨a.gates ++ b.gates ++ [⟨op,[a.output,b.output]⟩],start+a.size+b.size⟩

def emit (start : Nat) : Tree → Circuit
  | .input i => ⟨[],i.val⟩
  | .lit b => ⟨[⟨if b then .and else .or,[]⟩],start⟩
  | .meet a b =>
    let l := emit start a
    binary .and l (emit (start + l.size) b) start
  | .join a b =>
    let l := emit start a
    binary .or l (emit (start + l.size) b) start

private theorem binary_size (op : GateOp) (a b : Circuit) (start : Nat) :
    (binary op a b start).size = a.size+b.size+1 := by simp [binary,Circuit.size,Nat.add_assoc]

theorem emit_size (k : Nat) (t : Tree) : (emit k t).size = t.size := by
  induction t generalizing k with
  | input i => rfl
  | lit b => rfl
  | meet a b ha hb =>
    simp only [emit,binary_size,Tree.size,ha,hb]; omega
  | join a b ha hb =>
    simp only [emit,binary_size,Tree.size,ha,hb]; omega

def legalGate (g : Gate) := (match g.op with | .and | .or => true | _ => false) &&
  decide (g.inputs.length ≤ 2)

def accepts (t : Tree) := (emit 7 t).gates.all legalGate && (List.finRange 128).all (fun a =>
  let x := BitVec.ofNat 7 a.val
  (emit 7 t).eval (List.ofFn (fun i : Fin 7 => x.getLsbD i.val)) == t.eval x)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem verified_blocks : ∀ j s, ((repair j s).map accepts).getD true = true := by decide +kernel

theorem input_bits : ∀ x : Finset (Fin 7), input x = List.ofFn (fun i : Fin 7 => (maskOf x).getLsbD i.val) := by
  decide +kernel

theorem block_properties {j s t} (h : repair j s = some t) :
    (emit 7 t).size ≤ budget s ∧ (emit 7 t).gates.all legalGate = true ∧
    ∀ x : Finset (Fin 7), (emit 7 t).eval (input x) = t.eval (maskOf x) := by
  have cert := verified_blocks j s
  simp only [h,Option.map_some,Option.getD_some,accepts,Bool.and_eq_true,List.all_eq_true,
    beq_iff_eq] at cert
  refine ⟨(emit_size _ _).trans_le (repair_size h),List.all_eq_true.mpr cert.1,?_⟩
  intro x
  rw [input_bits]
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using cert.2 (⟨(maskOf x).toNat,(maskOf x).isLt⟩ : Fin 128) (by simp)

/-- The decoder sees the raw inputs and the result of the private block. -/
theorem replace_private_block {j s t} (h : repair j s = some t) (D : Circuit)
    (hm : binaryMono D.gates)
    (orig : ∀ x : Finset (Fin 7), D.eval (input x ++ [!DenseRepairs.signal j s (maskOf x)]) = graph (maskOf x)) :
    ∃ C : Circuit, C.size + D.size ≤ budget s + D.size ∧ C.gates.all legalGate = true ∧
      ∀ x : Finset (Fin 7), D.eval (input x ++ [C.eval (input x)]) = graph (maskOf x) := by
  obtain ⟨sz,ok,ev⟩ := block_properties h
  refine ⟨emit 7 t,by omega,ok,?_⟩
  have mono (x y : Finset (Fin 7)) (xy : x ≤ y) (a b : Bool) (ab : a ≤ b) :
      D.eval (input x ++ [a]) ≤ D.eval (input y ++ [b]) := by
    exact read_order (run_order hm (List.rel_append (input_order xy)
      (List.Forall₂.cons ab List.Forall₂.nil))) D.output
  intro x
  rw [ev]
  exact every_suffix h (fun y b => D.eval (input y ++ [b])) mono orig x

end PEqualNP.Research.DenseReplacementBlocks

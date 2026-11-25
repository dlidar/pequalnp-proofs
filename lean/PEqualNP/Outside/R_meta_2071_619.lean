import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

-- Pin the endpoints of the chosen flag to false. Every gate that reads a pinned
-- input disappears. The residual graph has 45 edges on the remaining 24 vertices.
-- Nine removed gates would leave at most 55, below the proposed residual bound.
theorem PEqualNP.Outside.R_meta_2071_619
    (hpin : ∀ (n : ℕ) (S : Finset (Fin n)) (C : Circuit), Monotone2 C →
      let pin := fun (x : Fin n → Bool) i => if i ∈ S then false else x i
      let count := C.gates.countP (fun g => g.inputs.any fun k => decide (∃ i ∈ S, (i : ℕ) = k))
      (∃ x, C.eval (List.ofFn (pin x)) = false) →
      ∃ R : Circuit, Monotone2 R ∧ R.size + count ≤ C.size ∧
        ∀ x, R.eval (List.ofFn x) = C.eval (List.ofFn (pin x)))
    (hres : let D : Finset (Fin 13) := {0,1,3,9}
    ∀ (p l : Fin 13), p-l ∈ D → ∀ R : Circuit, Monotone2 R →
      (∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 13, u ≠ p ∧ v ≠ l ∧ u - v ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true) → 56 ≤ R.size)
    (hlow : let D : Finset (Fin 13) := {0,1,3,9}
    ∀ (C : Circuit) (p l : Fin 13), let S : Finset (Fin 26) := {Fin.castAdd 13 p, Fin.natAdd 13 l}
      C.size ≤ 64 → C.gates.countP (fun g => g.inputs.any fun k => decide (∃ z ∈ S, (z : ℕ) = k)) ≤ 8 →
      IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 13, u - v ∈ D ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true) →
      0 < andPairs 26 C →
      (∃ k < C.size, (gateAt C k).op = .and ∧ ∃ x,
        gateVal 26 C k x = true ∧ C.eval (List.ofFn x) = false) →
      p-l ∈ D → PEqualNP.ReadK.lineSingle C 26 (fun i => i == (13+l.val)) p.val (13+l.val) = true ∨ PEqualNP.ReadK.lineSingle C 26 (fun i => i == p.val) (13+l.val) p.val = true)
    (htrack : ∀ (C : Circuit) (a b : Fin 26) (d : ℕ → Bool),
      let w := fun j => wireVal 26 C j (pairInput a a)
      a ≠ b → IsAO2 26 C →
      (∀ i < 26, d i = decide (i = b.val)) →
      (∀ k (g : Gate) u v, C.gates[k]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (26+k) = ((w u && d v) || (d u && w v))) ∧
        (g.op = .or → d (26+k) = (d u || d v))) →
      PEqualNP.ReadK.lineSingle C 26 (fun i => i == b.val) a.val b.val = true →
      d C.output = true) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  classical
  dsimp only
  intro C p l f h hsize hgates heval hnested hdirty hinc hf hh
  have hgateFacts (g : PEqualNP.CircuitLowerBounds.Gate) (hm : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨hop, u, v, hargs, hne, _, _⟩ := hgates k g hk
    exact ⟨hop, by simp [hargs], by simp [hargs, hne]⟩
  have hshape : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hm => (hgateFacts g hm).1, ?_, fun g hm => (hgateFacts g hm).2.1⟩
    intro k hk w hw
    have hgate : C.gates[k]? = some C.gates[k] := by simp [hk]
    obtain ⟨_, u, v, hargs, _, hu, hv⟩ := hgates k C.gates[k] hgate
    change w ∈ (C.gates.getD k ⟨.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem _ _ hk, hargs] at hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  have hdistinct : ∀ g ∈ C.gates, g.inputs.Nodup := fun g hm => (hgateFacts g hm).2.2
  let S : Finset (Fin 26) := {Fin.castAdd 13 p, Fin.natAdd 13 l}
  let count := C.gates.countP (fun g => g.inputs.any fun k => decide (∃ z ∈ S, (z : ℕ) = k))
  have hmono : Monotone2 C := fun g hg => ⟨(hgateFacts g hg).1, le_of_eq (hgateFacts g hg).2.1⟩
  let pin := fun (x : Fin 26 → Bool) (i : Fin 26) => if i ∈ S then false else x i
  have noEdge : C.eval (List.ofFn (pin (fun _ => false))) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨u,v,_,hu,_⟩ := (heval _).mp ht
    simp [pin] at hu
  obtain ⟨R,hm,number,eqR⟩ := hpin 26 S C hmono ⟨_,noEdge⟩
  have hp (u : Fin 13) : Fin.castAdd 13 u ∈ S ↔ u = p := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
    change (u.val = p.val ∨ u.val = 13+l.val) ↔ u.val = p.val
    have := u.isLt
    omega
  have hl (v : Fin 13) : Fin.natAdd 13 v ∈ S ↔ v = l := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
    change (13+v.val = p.val ∨ 13+v.val = 13+l.val) ↔ v.val = l.val
    have := p.isLt
    omega
  have bound := hres p l hinc R hm (by
    intro x
    rw [eqR, heval]
    constructor
    · rintro ⟨u,v,hi,hu,hv⟩
      by_cases up : u = p
      · simp only [hp, ite_eq_left up, Bool.false_eq_true] at hu
      by_cases vl : v = l
      · simp only [hl, ite_eq_left vl, Bool.false_eq_true] at hv
      exact ⟨u,v,up,vl,hi,by simpa only [hp,ite_eq_right up] using hu,by simpa only [hl,ite_eq_right vl] using hv⟩
    · rintro ⟨u,v,up,vl,hi,hu,hv⟩
      exact ⟨u,v,hi,by simpa only [hp,ite_eq_right up] using hu,by simpa only [hl,ite_eq_right vl] using hv⟩)
  change R.size + count ≤ C.size at number
  have hc : count ≤ 8 := by omega
  have hne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro h
    have t := congrArg Fin.val h
    change p.val = 13 + l.val at t
    have := p.isLt
    omega
  have singleton (a : Fin 26) : pairInput a a = fun i => decide (i = a) := by
    funext i
    change decide (i = a ∨ i = a) = decide (i = a)
    simp only [or_self]
  rcases hlow C p l hsize hc hshape hdistinct heval hnested hdirty hinc with hs | hs
  · left
    apply htrack C (Fin.castAdd 13 p) (Fin.natAdd 13 l) f hne hshape hf.1 _ hs
    intro k g u v hg huv
    change (g.op = .and → f (26+k) = (((C.wires (List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.castAdd 13 p)))).getD u false && f v) ||
      (f u && (C.wires (List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.castAdd 13 p)))).getD v false))) ∧ _
    rw [singleton]
    exact hf.2 k g u v hg huv
  · right
    apply htrack C (Fin.natAdd 13 l) (Fin.castAdd 13 p) h hne.symm hshape hh.1 _ hs
    intro k g u v hg huv
    change (g.op = .and → h (26+k) = (((C.wires (List.ofFn (pairInput (Fin.natAdd 13 l) (Fin.natAdd 13 l)))).getD u false && h v) ||
      (h u && (C.wires (List.ofFn (pairInput (Fin.natAdd 13 l) (Fin.natAdd 13 l)))).getD v false))) ∧ _
    rw [singleton]
    exact hh.2 k g u v hg huv

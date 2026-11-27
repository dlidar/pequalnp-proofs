import Gadgets
namespace SpinCircuit
open Finset PEqualNP.CircuitLowerBounds
structure Encoding (X : Type) (n : ℕ) where
  base : X → List Bool
  length : ∀ x, (base x).length = n
  enough : 2 ≤ n
  zero : ∀ x, (base x).getD 0 false=false
  one : ∀ x, (base x).getD 1 false=true

variable {X : Type} {n : ℕ} (E : Encoding X n)
def level (U r : ℕ) (f : X → Bool) := built n E.base f (U^r)

theorem constant (b : Bool) : built n E.base (fun _ => b) 0 := by
  cases b with
  | false =>
    have h := read_input E.base E.length (⟨0,by have := E.enough;omega⟩ : Fin n)
    simpa only [Fin.val_mk,E.zero] using h
  | true =>
    have h := read_input E.base E.length (⟨1,by have := E.enough;omega⟩ : Fin n)
    simpa only [Fin.val_mk,E.one] using h

theorem bool_not {B : ℕ} {f : X → Bool} (h : built n E.base f B) : built n E.base (fun x => !f x) (B+1) := by
  intro M hM
  obtain ⟨p,o,hp,hl,ho,he⟩ := h M hM
  let q : List Gate := [⟨.not,[o]⟩]
  have hq : legal (M+p.length) q := by
    intro j hj
    have hj' : j<1 := hj
    have : j=0 := by omega
    subst j;simp [q,allowed,ho]
  refine ⟨p++q,M+p.length,legal_append hp hq,by simp [q];omega,by simp [q,Nat.add_assoc],?_⟩
  intro x w hw hh
  have hv : (run p w).length=M+p.length := by rw [run_length,hw]
  change _ = !f x
  rw [run_append,← hv,← he x w hw hh]
  simp [run,q,GateOp.eval]

def onCount {l : ℕ} (f : Fin l → X → Bool) (x : X) : ℕ := ∑ i, (f i x).toNat

theorem threshold {l B : ℕ} (fs : Fin l → X → Bool) (hf : ∀ i, built n E.base (fs i) B) (a : ℕ) :
    built n E.base (fun x => decide (a ≤ onCount fs x)) (l*B + l*((l+1)*2)) := by
  by_cases ha : a ≤ l
  · intro M hM
    obtain ⟨p,o,hp,hl,ho,he⟩ := indexed fs hf M hM
    let J := M+p.length
    have hvalid (i) (hi : i ∈ List.ofFn o) : i<J := by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi;exact ho j
    obtain ⟨q,z,hq,hlq,hz,hev⟩ := unary J l (by dsimp [J];have := E.enough;omega) (List.ofFn o) hvalid
    let j : Fin (l+1) := ⟨a,by omega⟩
    refine ⟨p++q,z j,legal_append hp hq,?_,by simpa [J,Nat.add_assoc] using hz j,?_⟩
    · simpa using Nat.add_le_add hl hlq
    · intro x w hw hprefix
      have hv : (run p w).length=J := by rw [run_length,hw]
      have old (i : ℕ) (hi : i<n) : (run p w).getD i false = (E.base x).getD i false := by
        obtain ⟨ts,ht⟩ := hprefix.trans (extends_run p w)
        rw [← ht,List.getD_append _ _ _ _ (by rw [E.length];exact hi)]
      rw [run_append,hev _ hv ((old 0 (by have := E.enough;omega)).trans (E.zero _))
        ((old 1 (by have := E.enough;omega)).trans (E.one _)) j]
      have hx : ones (List.ofFn o) (run p w) = onCount fs x := by
        unfold ones onCount
        rw [List.map_ofFn]
        have hh : (fun j => (run p w).getD (o j) false) = fun j => fs j x := funext (he x w hw hprefix)
        change (List.ofFn (fun j => (run p w).getD (o j) false)).count true = _
        rw [hh,← List.sum_ofFn]
        have hcount (s : List Bool) : s.count true = (s.map Bool.toNat).sum := by
          induction s with
          | nil => rfl
          | cons u us ih => cases u <;> simp [List.count_cons,ih,Nat.add_comm]
        rw [hcount,List.map_ofFn];rfl
      rw [hx]
  · have hx (x : X) : ¬ a ≤ onCount fs x := by
      have hh := sum_le_sum (s := (univ : Finset (Fin l))) (g := fun _ => 1) (fun i _ => Bool.toNat_le (fs i x))
      have hl : onCount fs x ≤ l := by simpa [onCount] using hh
      omega
    simp only [hx,decide_false]
    exact weaken (constant E false) (Nat.zero_le _)

theorem lift_level {U r v : ℕ} (hU : 1 ≤ U) (hv : r≤v) {f : X→Bool} (hf : level E U r f) : level E U v f :=
  weaken hf (Nat.pow_le_pow_right hU hv)
theorem level_const (U r : ℕ) (b : Bool) : level E U r (fun _ => b) := weaken (constant E b) (Nat.zero_le _)
theorem level_not {U r : ℕ} (hU : 4 ≤ U) {f : X→Bool} (hf : level E U r f) : level E U (r+1) (fun x => !f x) := by
  apply weaken (bool_not E hf)
  rw [pow_succ]
  have hp : 0 < U^r := by positivity
  nlinarith
theorem level_threshold {U r l : ℕ} (hU : 4 ≤ U) (hl : l ≤ U) (fs : Fin l → X → Bool)
    (hf : ∀ i, level E U r (fs i)) (a : ℕ) : level E U (r+4) (fun x => decide (a ≤ onCount fs x)) := by
  apply weaken (threshold E fs hf a)
  have hh := Nat.mul_le_mul_right (U^r) hl
  have hg := Nat.mul_le_mul hl (Nat.mul_le_mul_right 2 (Nat.add_le_add_right hl 1))
  have hp : 1 ≤ U^r := Nat.one_le_pow _ _ (by omega)
  rw [pow_add]
  have hs : 4 ≤ U*U := by nlinarith
  have h₁ : U + U*((U+1)*2) ≤ U^4 := by
    have h := Nat.mul_le_mul_left (U*U) hs
    nlinarith
  have h₂ := Nat.mul_le_mul_left (U*((U+1)*2)) hp
  have h₃ := Nat.mul_le_mul_left (U^r) h₁
  nlinarith
end SpinCircuit

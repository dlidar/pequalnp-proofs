import PEqualNP.Research.L_meta_10633_repairs
import PEqualNP.Research.L_meta_10633_formula
namespace PEqualNP.Research.DenseGraphPanels
open PEqualNP.Research.DenseRepairs PEqualNP.Research.BinaryFormulaPanels

def maximalIndependent : List Mask := [7,12,18,24,36,65]

theorem positive_rows : ∀ e ∈ edgeMasks, graph e = true := by decide +kernel
theorem negative_rows : ∀ e ∈ maximalIndependent, graph e = false := by decide +kernel
theorem boundary : ∀ x : Mask,
    (if graph x then edgeMasks.any (fun e => (e &&& x) == e)
    else maximalIndependent.any (fun n => (n &&& x) == x)) = true := by decide +kernel

def Increasing (f : Mask → Bool) := ∀ x y, x &&& y = x → f x ≤ f y

theorem exact_tests (f : Mask → Bool) (h : Increasing f) :
    (∀ x, f x = graph x) ↔ (∀ e ∈ edgeMasks, f e = true) ∧
    (∀ n ∈ maximalIndependent, f n = false) := by
  constructor
  · intro ex
    exact ⟨fun e he => (ex e).trans (positive_rows e he),fun n hn => (ex n).trans (negative_rows n hn)⟩
  · rintro ⟨p,n⟩ x
    have test := boundary x
    cases gx : graph x
    · simp only [gx,Bool.false_eq_true,ite_false,List.any_eq_true,beq_iff_eq] at test
      obtain ⟨a,ha,sub⟩ := test
      have le := h x a (by rwa [BitVec.and_comm])
      rw [n a ha] at le
      exact Bool.eq_false_of_le_false le
    · simp only [gx,ite_true,List.any_eq_true,beq_iff_eq] at test
      obtain ⟨a,ha,sub⟩ := test
      have le := h a x sub
      rw [p a ha] at le
      exact Bool.eq_true_of_true_le le

def standardFormula : Formula (Fin 7) := (.meet (.join (.leaf 1) (.join (.leaf 3) (.join (.leaf 4) (.meet (.join (.leaf 2) (.leaf 5)) (.join (.leaf 0) (.leaf 6)))))) (.join (.join (.join (.leaf 5) (.leaf 6)) (.meet (.leaf 4) (.join (.leaf 0) (.leaf 2)))) (.meet (.leaf 3) (.join (.leaf 0) (.leaf 1)))))

theorem formula_size : standardFormula.gates = 14 := rfl
theorem formula_exact : ∀ x : Mask, standardFormula.value (fun i => x.getLsbD i.val) = graph x := by
  decide +kernel

theorem formula_mono (t : Formula (Fin 7)) : Increasing (fun x => t.value (fun i => x.getLsbD i.val)) := by
  intro x y sub
  induction t with
  | leaf i =>
    have eq := congrArg (fun w : Mask => w.getLsbD i.val) sub
    change x.getLsbD i.val ≤ y.getLsbD i.val
    simp only [BitVec.getLsbD_and] at eq
    exact (by decide : ∀ a b : Bool, (a && b) = a → a ≤ b) _ _ eq
  | meet a b ha hb =>
    exact (by decide : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d)) _ _ _ _ ha hb
  | join a b ha hb =>
    exact (by decide : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d)) _ _ _ _ ha hb

theorem partition_target (k : Nat) :
    Partition (fun (x : Mask) (i : Fin 7) => x.getLsbD i.val)
      edgeMasks.toFinset maximalIndependent.toFinset k ↔
    ∃ t : Formula (Fin 7), t.gates = k ∧ ∀ x : Mask, t.value (fun i => x.getLsbD i.val) = graph x := by
  rw [exact_cost]
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  rw [exact_tests _ (formula_mono t)]
  simp [Separates]

end PEqualNP.Research.DenseGraphPanels

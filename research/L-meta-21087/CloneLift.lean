import Family
open PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Mask114591Family Mask114591Support

namespace Mask114591CloneLift

def index (n p i : Nat) :=
  if i < n then (if i = p then n+1 else i) else i+2

def rename (n p : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (index n p)⟩

def lift (n p : Nat) (C : Circuit) : Circuit :=
  ⟨⟨.or,[p,n]⟩ :: C.gates.map (rename n p),index n p C.output⟩

theorem simulate (n p : Nat) (gs : List Gate) (a b : List Bool)
    (init : n ≤ a.length) (len : b.length = a.length+2)
    (reads : ∀ i, b.getD (index n p i) false = a.getD i false) :
    ∀ i, ((gs.map (rename n p)).foldl step b).getD (index n p i) false =
      (gs.foldl step a).getD i false := by
  induction gs generalizing a b with
  | nil => exact reads
  | cons g gs ih =>
    apply ih
    · simp [step] <;> omega
    · simp [step,len]
    · intro i
      simp only [step,append_bit,rename,List.map_map]
      have ev : (g.inputs.map ((fun j => b.getD j false) ∘ index n p)) =
          (g.inputs.map fun j => a.getD j false) := by
        apply List.map_congr_left
        intro j _
        exact reads j
      rw [ev]
      have he : index n p i = b.length ↔ i = a.length := by
        simp only [index]; split_ifs <;> omega
      simp only [he,reads]

theorem lift_size (n p : Nat) (C : Circuit) : (lift n p C).size = C.size+1 := by
  simp [lift,Circuit.size]

theorem lift_mono (n p : Nat) {C : Circuit} (hc : Monotone2 C) : Monotone2 (lift n p C) := by
  intro g hg
  rcases List.mem_cons.mp hg with he | hg
  · subst g; simp
  · obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    simpa [rename] using hc g' hg'

def projectLast {m : Nat} (p : Fin m) (v : Fin (m+1)) : Fin m :=
  if h : v.val < m then ⟨v.val,h⟩ else p

theorem lift_rep {n m : Nat} (p : Fin m) {A : Fin n → Fin m → Bool} {C : Circuit}
    (hr : Represents A C) :
    Represents (fun u v => A u (projectLast p v)) (lift (n+m) (n+p.val) C) := by
  intro u v
  let q := projectLast p v
  let a := oneEach u q
  let x := oneEach u v
  let b := step x ⟨.or,[n+p.val,n+m]⟩
  have ha : a.length = n+m := by simp [a,oneEach] <;> omega
  have hx : x.length = n+m+1 := by simp [x,oneEach] <;> omega
  have hb : b.length = a.length+2 := by simp [b,step,ha,hx]
  apply Eq.trans _ (hr u q)
  apply simulate _ _ C.gates a b (by omega) hb
  intro i
  dsimp only [b,step]
  rw [append_bit,hx]
  simp only [a,x,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,oneEach_bit,q,projectLast,index]
  split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [Bool.or_eq_true,decide_eq_true_eq] <;> omega

end Mask114591CloneLift
#print axioms Mask114591CloneLift.lift_rep

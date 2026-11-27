import Cut
import Reference
namespace Graph32249
open MonotoneCut
structure Four where
  val : Fin 16
  deriving DecidableEq, Fintype
def below (a b : Four) : Prop := a.val.val &&& b.val.val = a.val.val
instance (a b : Four) : Decidable (below a b) := inferInstanceAs (Decidable (_ = _))
instance : Preorder Four where
  le := below
  le_refl := by decide +kernel
  le_trans := by decide +kernel
instance (a b : Four) : Decidable (a≤b) := inferInstanceAs (Decidable (below a b))
def signal (v : Fin 16 → Nat) (a : Four) {k : Nat} (j : Fin k) := (v a.val).testBit j.val
def rowFunction (r : Fin 16 → Nat) (a b : Four) : Bool := (r a.val).testBit b.val.val
def Can (F : Four → Four → Bool) (k : Nat) := ∃ e : Four → Fin k → Bool,Works F e

def Checks (k : Nat) (v r : Fin 16 → Nat) : Prop :=
   (∀ a b : Four,a≤b → ∀j : Fin k, signal v a j ≤ signal v b j) ∧
   (∀ a b : Four,(∀j : Fin k,signal v a j ≤ signal v b j) → ∀ q,rowFunction r a q≤rowFunction r b q) ∧
   (∀ a b c : Four,b≤c → rowFunction r a b≤rowFunction r a c)
instance (k : Nat) (v r : Fin 16 → Nat) : Decidable (Checks k v r) := by unfold Checks;infer_instance

theorem from_checks {k : Nat} {v r : Fin 16 → Nat} (ok : Checks k v r) : Can (rowFunction r) k := by
  refine ⟨(fun a (j : Fin k) => signal v a j), (works_iff _ _ (fun a _ _ h => ok.2.2 a _ _ h)).2 ⟨?_,?_⟩⟩
  · intro a b h j;exact ok.1 a b h j
  · intro a b h q;exact ok.2.1 a b h q

def mkPair (a b : Fin 16) : Four × Four := (⟨a⟩,⟨b⟩)
def splitInput (order : Fin 8 → Nat) (a b : Four) (i : Fin 8) : Bool :=
  if order i<4 then a.val.val.testBit (order i) else b.val.val.testBit (order i-4)

theorem smaller {F : Four → Four → Bool} {k l : Nat} (h : Can F k) (kl : k≤l) : Can F l := by
  obtain ⟨e,he,D,hD,hR,works⟩ := h
  let enc := fun a (j : Fin l) => if z : j.val<k then e a ⟨j.val,z⟩ else false
  let drop := fun (z : Fin l → Bool) (i : Fin k) => z (i.castLE kl)
  have hd : Monotone drop := by intro u v h i;exact h _
  refine ⟨enc,?_,(fun z => D (drop z)), (hD.comp hd),fun z => hR _,?_⟩
  · intro a b h j;dsimp [enc];split <;> first | exact he h _ | exact le_rfl
  · intro a b
    have eq : drop (enc a)=e a := by funext i;simp [enc,drop,i.isLt]
    change D (drop (enc a)) b = F a b
    rw [eq];exact works a b
end Graph32249

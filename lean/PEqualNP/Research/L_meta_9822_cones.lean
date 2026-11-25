import PEqualNP.Research.L_meta_9822_root

namespace PEqualNP.Research.PuncturedPetersen
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 100000

def Full (u : Nat → Bool) := ∀ i : Fin 10, ¬ Omits u i.val

theorem essential (p : Fin 10) : ¬ Omits target p.val := by
  have cert : ∀ i : Fin 10, ∃ x : Fin 1024, target (x.val ||| 2^i.val) ≠ target x.val := by decide +kernel
  obtain ⟨x,h⟩ := cert p; exact fun skip => h (skip _)

theorem full_and (u v : Nat → Bool) (comp : ∀ x, (u x && v x) = target x) : Full u ∨ Full v := by
  by_contra! h
  obtain ⟨p,hp⟩ : ∃ p : Fin 10, Omits u p.val := by simpa [Full] using h.1
  obtain ⟨q,hq⟩ : ∃ q : Fin 10, Omits v q.val := by simpa [Full] using h.2
  have andCode : ∀ a b : Bool, gate 8 a b = (a && b) := by decide
  rcases lt_trichotomy p q with lt | eq | gt
  · have hh := (root_constraint 8 v u p q lt hq hp (fun x => by rw [andCode,Bool.and_comm,comp])).1
    rcases hh with h | h | h | h <;> contradiction
  · subst q
    apply essential p
    intro x; rw [← comp,← comp,hp x,hq x]
  · have hh := (root_constraint 8 u v q p gt hp hq (fun x => by rw [andCode,comp])).1
    rcases hh with h | h | h | h <;> contradiction

def value (C : Circuit) (w x : Nat) := (C.wires (List.ofFn (fun i : Fin 10 => x.testBit i.val))).getD w false
def withFinal (C : Circuit) (op : GateOp) (a b : Nat) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩],10+C.size⟩

theorem final_and_eval (C : Circuit) (a b x : Nat) :
    (withFinal C .and a b).eval (List.ofFn (fun i : Fin 10 => x.testBit i.val)) =
    (value C a x && value C b x) := by
  let input := List.ofFn (fun i : Fin 10 => x.testBit i.val)
  have len : (C.wires input).length = 10+C.size := by
    unfold Circuit.wires Circuit.size
    have step (gs : List Gate) (w : List Bool) : (gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons,ih]; simp; omega
    simpa [input] using step C.gates input
  unfold withFinal Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change (((C.wires input) ++ [GateOp.and.eval ([a,b].map fun i => (C.wires input).getD i false)]).getD (10+C.size) false) = _ 
  rw [← len]
  simp [GateOp.eval,value,input]

/-- Applies to arbitrary sharing and arbitrary prefix operations, including NOT. -/
theorem final_and_full_support (C : Circuit) (a b : Nat)
    (correct : ∀ x : Fin 10 → Bool, (withFinal C .and a b).eval (List.ofFn x) = targetBits x) :
    Full (value C a) ∨ Full (value C b) := by
  apply full_and
  intro x
  rw [← final_and_eval,correct,target_exact]

end PEqualNP.Research.PuncturedPetersen

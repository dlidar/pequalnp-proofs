import Reference
import Convert
namespace Graph29707
open InverterBridge PEqualNP.Research.TripleFormulaMass
def singleton (i : Fin 8) (j : Fin 8) := decide (j=i)
def pair (i k : Fin 8) (j : Fin 8) := decide (j=i ∨ j=k)
def neighbor (i : Fin 8) : Fin 8 := if i=0 then 4 else if i=1 then 5 else if i=2 then 5 else if i=3 then 6 else 0

theorem essential : ∀ i, ∃ x y : Fin 8 → Bool, x≤y ∧ (∀ j,j≠i → x j=y j) ∧ target x=false ∧ target y=true := by
  have cert : ∀ i : Fin 8, target (singleton (neighbor i))=false ∧ target (pair i (neighbor i))=true := by decide +kernel
  intro i; refine ⟨_,_,?_,?_,(cert i).1,(cert i).2⟩
  · intro j; by_cases h : j=neighbor i <;> simp [singleton,pair,h]
  · intro j ne; simp [singleton,pair,ne]

def expression (x : Fin 8 → Bool) := (x 0 ⊓ x 4) ⊔ (x 0 ⊓ x 5) ⊔ (x 1 ⊓ x 5) ⊔ (x 2 ⊓ x 5) ⊔ (x 0 ⊓ x 6) ⊔ (x 1 ⊓ x 6) ⊔ (x 3 ⊓ x 6) ⊔ (x 4 ⊓ x 6) ⊔ (x 0 ⊓ x 7) ⊔ (x 2 ⊓ x 7) ⊔ (x 4 ⊓ x 7) ⊔ (x 5 ⊓ x 7)

theorem expression_eq : ∀ x,target x=expression x := by decide +kernel
theorem mono : Monotone target := by
  intro x y h
  rw [expression_eq,expression_eq]
  unfold expression
  repeat' apply sup_le_sup
  all_goals exact inf_le_inf (h _) (h _)

theorem small_inverter_decoder (c : Context (Fin 8)) (G : X (Fin 8) → Bool) (anti : Antitone G)
    (ok : ∀ x,c.eval x (G x)=target x) (small : c.rawLeaves≤10) :
    ∃ f : Formula (Fin 8), f.leaves≤11 ∧ ∀ x,f.eval x=target x := by
  have eq : (fun x => c.eval x (G x))=target := funext ok
  obtain ⟨f,hf,he⟩ := c.small_decoder G anti (by rw [eq]; exact mono) (by simpa only [ok] using essential)
    (by simpa using small)
  exact ⟨f,by omega,fun x => (he x).trans (ok x)⟩
end Graph29707

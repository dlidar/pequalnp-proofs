import PEqualNP.Outside.L_meta_1018
namespace PEqualNP.Research.SingleInverter
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1018

abbrev MonoGates (gs : List Gate) := ∀ g∈gs,g.op=.and ∨ g.op=.or
abbrev Signal (n : Nat) := Fin n → Bool
abbrev Extends {n} (x y : Signal n) := ∀ i,x i=true → y i=true

/-- A monotone continuation with a separately controlled inverter wire must copy it
    if the actual circuit reverses the two endpoint assignments. -/
theorem context_identity {n} (h : Signal n → Bool → Bool) (inv : Signal n → Bool)
    (mono : ∀ x y a b, Extends x y → (a=true → b=true) → h x a=true → h y b=true)
    (lo : h (fun _ => false) (inv (fun _ => false))=true)
    (hi : h (fun _ => true) (inv (fun _ => true))=false) : ∀ x t,h x t=t := by
  have bitLo : inv (fun _ => false)=true := by
    cases a : inv (fun _ => false) with
    | true => rfl
    | false =>
      have z := mono _ (fun _ => true) _ (inv (fun _ => true)) (fun _ _ => rfl) (by rw [a];simp) lo
      rw [hi] at z
      contradiction
  have bitHi : inv (fun _ => true)=false := by
    cases b : inv (fun _ => true) with
    | false => rfl
    | true =>
      have z := mono _ (fun _ => true) _ (inv (fun _ => true)) (fun _ _ => rfl) (by simp [b]) lo
      rw [hi] at z
      contradiction
  rw [bitLo] at lo
  rw [bitHi] at hi
  intro x t
  cases t with
  | true => exact mono _ _ _ _ (by intro i h;contradiction) id lo
  | false =>
    cases z : h x false with
    | false => rfl
    | true =>
      have hit := mono _ _ _ false (fun _ _ => rfl) id z
      rw [hi] at hit
      contradiction

def controlled {n} (pre post : List Gate) (o : Nat) (x : Signal n) (t : Bool) :=
  (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [t])).getD o false

theorem controlled_mono {n} (pre post : List Gate) (a : MonoGates pre) (b : MonoGates post)
    (o : Nat) (x y : Signal n) (u v : Bool) (xy : Extends x y) (uv : u=true → v=true) :
    controlled pre post o x u=true → controlled pre post o y v=true := by
  apply wiresFrom_mono post b _ _ (by simp [length_wiresFrom])
  intro i
  simp only [getD_snoc, length_wiresFrom, List.length_ofFn]
  split_ifs with h eq
  · apply wiresFrom_mono pre a _ _ (by simp)
    intro j
    by_cases hj : j<n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
      simp only [List.getElem_ofFn]
      exact xy _
    · simp [List.getD_eq_default, Nat.le_of_not_lt hj]
  · exact uv
  · exact id

def inverse {n} (pre : List Gate) (args : List Nat) (x : Signal n) :=
  GateOp.not.eval (args.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)

theorem split_eval {n} (pre post : List Gate) (args : List Nat) (o : Nat) (x : Signal n) :
    (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.ofFn x)=
      controlled pre post o x (inverse pre args x) := by
  simp [Circuit.eval,Circuit.wires,controlled,inverse,wiresFrom,List.foldl_append]

theorem remove_suffix {n} (pre post : List Gate) (args : List Nat) (o : Nat)
    (a : MonoGates pre) (b : MonoGates post)
    (lo : (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.replicate n false)=true)
    (hi : (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.replicate n true)=false)
    (x : Signal n) :
    (Circuit.mk (pre ++ ⟨.not,args⟩ :: post) o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ [⟨.not,args⟩]) (n+pre.length)).eval (List.ofFn x) := by
  have eq := context_identity (controlled pre post o) (inverse pre args)
    (controlled_mono pre post a b o)
    (by rw [← split_eval]; simpa using lo) (by rw [← split_eval]; simpa using hi)
  rw [split_eval,eq]
  change _ = (wiresFrom (pre ++ [⟨.not,args⟩]) (List.ofFn x)).getD _ false
  rw [wiresFrom_snoc,getD_snoc]
  simp [length_wiresFrom,inverse]

end PEqualNP.Research.SingleInverter

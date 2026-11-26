import PEqualNP.MetaComplexity.Helpers.ForestElim
import PEqualNP.MetaComplexity.L106

namespace PEqualNP.Research.GateCuts3321
open PEqualNP.MetaComplexity

abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool
def cut {n} (f : Fn n) (i : Fin n) (b : Bool) : Fn n := fun x => f (Function.update x i b)
def Lower {n} (f : Fn n) (k : ℕ) := ∀ s, HasCircuitSize n f s → k ≤ s
def Dep {n} (f : Fn n) (i : Fin n) := ∃ x, f (Function.update x i (!x i)) ≠ f x
def Nonconst {n} (f : Fn n) := ∃ x y, f x ≠ f y
def Ignores {n} (f : Fn n) (i : Fin n) := ∀ x b, f (Function.update x i b) = f x

theorem one_step {n k} {f : Fn (n+1)} {i} {b} (hk : 0 < k)
    (dep : Dep f i) (nc : Nonconst (cut f i b)) (low : Lower (cut f i b) k) : Lower f (k+1) := by
  intro s hs
  obtain ⟨C,fan,sz,ev⟩ := hs
  have h : HasCircuitSize (n+1) f ((s-1)+1) := ⟨C,fan,by omega,ev⟩
  have a := low (s-1) (Helpers.Forest.one_gate_at n f i b (s-1) dep nc h)
  omega

theorem two_steps {n k} {f : Fn (n+1)} {i} (dep : Dep f i)
    (nc : ∀ b, Nonconst (cut f i b)) (low : ∀ b, Lower (cut f i b) k) : Lower f (k+2) := by
  intro s hs
  obtain ⟨b,s',cost,h⟩ := Helpers.PermInputs.gate_elim_at n f i s dep nc hs
  have := low b s' h
  omega

theorem flip_witness {n} (f : Fn n) (i : Fin n) (x : Fin n → Bool)
    (diff : cut f i false x ≠ cut f i true x) : Dep f i := by
  refine ⟨Function.update x i false,?_⟩
  simpa [cut,Function.update_idem] using diff.symm

def leaf {n} (f h : Fn n) (v : Fin n) : Fn n := fun x => f x || (x v && h x)

theorem leaf_cost {n k} {f h : Fn (n+1)} {v} (fk : Lower f k) (hk : 0 < k)
    (nc : Nonconst f) (fv : Ignores f v) (hv : Ignores h v)
    (edge : ∃ x, f x = false ∧ h x = true) : Lower (leaf f h v) (k+1) := by
  unfold Ignores at fv hv
  have zero : cut (leaf f h v) v false = f := by funext x;simp [cut,leaf,fv]
  apply one_step (f:=leaf f h v) (i:=v) (b:=false) hk _ (by rw [zero];exact nc) (by rw [zero];exact fk)
  obtain ⟨x,a,b⟩ := edge
  apply flip_witness _ _ x
  simp [leaf,cut,fv,hv,a,b]

def tail {n} (f h : Fn n) (u v : Fin n) : Fn n :=
  fun x => f x || (x v && (h x || x u))

theorem tail_cost {n k} {f h : Fn (n+1)} {u v : Fin (n+1)} (diff : u ≠ v)
    (fk : Lower f k) (hk : 0 < k) (nc : Nonconst f)
    (fu : Ignores f u) (fv : Ignores f v) (hu : Ignores h u) (hv : Ignores h v)
    (both : ∀ b : Bool, ∃ x, f x = false ∧ h x = b) : Lower (tail f h u v) (k+3) := by
  unfold Ignores at fu fv hu hv
  have branch (b : Bool) : cut (tail f h u v) u b = leaf f (fun x => h x || b) v := by
    funext x;simp [cut,tail,leaf,fu,hu,Function.update_of_ne diff.symm]
  apply two_steps (k:=k+1) (i:=u)
  · obtain ⟨x,fa,ha⟩ := both false
    apply flip_witness _ _ (Function.update x v true)
    simp [branch,leaf,fv,hv,fa,ha]
  · intro b;rw [branch]
    obtain ⟨x,y,xy⟩ := nc
    exact ⟨Function.update x v false,Function.update y v false,by simpa [leaf,fv] using xy⟩
  · intro b;rw [branch]
    obtain ⟨x,fa,ha⟩ := both true
    exact leaf_cost fk hk nc fv (fun w c => by simp [hv]) ⟨x,fa,by simp [ha]⟩

def six : Fn 6 := fun x => decide (∃ i j : Fin 6, (i.val+1)%6=j.val ∧ x i=true ∧ x j=true)

theorem contains_six {n} (f : Fn n) (π : Fin n → Fin 6) (ident : ∀ x, f (x ∘ π) = six x) :
    Lower f 8 := by
  intro s hs
  have h := Helpers.PermInputs.relabel_size π _ _ hs
  rw [show (fun x => f (x ∘ π)) = six from funext ident] at h
  have := (L106 6 s (by decide)).mp h
  omega
end PEqualNP.Research.GateCuts3321

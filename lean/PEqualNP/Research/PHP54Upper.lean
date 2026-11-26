import PEqualNP.Defs.ProofComplexity

namespace PEqualNP.Research.PHP54

open PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
abbrev C := Clause V

inductive Step where
  | pigeon (i : Fin 5)
  | hole (i k : Fin 5) (j : Fin 4)
  | resolve (a b : Nat) (v : V)

def step : Step → List C → Option C
  | .pigeon i, _ => some (Finset.univ.image (fun j : Fin 4 => ((i,j),true)))
  | .hole i k j, _ => if i ≠ k then some {((i,j),false),((k,j),false)} else none
  | .resolve a b v, cs => do
    let x ← cs[a]?
    let y ← cs[b]?
    if (v,true) ∈ x ∧ (v,false) ∈ y then
      some (x.erase (v,true) ∪ y.erase (v,false))
    else none

theorem step_sound {s cs c} (h : step s cs = some c) (d : IsDerivation (PHP 5 4) cs) :
    IsDerivation (PHP 5 4) (c::cs) := by
  cases s with
  | pigeon i =>
    simp [step] at h
    subst c
    exact .ax d (Or.inl ⟨i,rfl⟩)
  | hole i k j =>
    by_cases hik : i ≠ k
    · simp [step,hik] at h
      subst c
      exact .ax d (Or.inr ⟨i,k,j,hik,rfl⟩)
    · simp [step,hik] at h
  | resolve a b v =>
    cases hx : cs[a]? with
    | none => simp [step,hx] at h
    | some x =>
      cases hy : cs[b]? with
      | none => simp [step,hx,hy] at h
      | some y =>
        by_cases hp : (v,true) ∈ x ∧ (v,false) ∈ y
        · simp [step,hx,hy,hp] at h
          exact .res d (List.mem_of_getElem? hx) (List.mem_of_getElem? hy) ⟨v,hp.1,hp.2,h.symm⟩
        · simp [step,hx,hy,hp] at h

def run : List Step → List C → Option (List C)
  | [], cs => some cs
  | s::ss, cs => (step s cs).bind (fun c => run ss (c::cs))

theorem run_sound {ss cs out} (h : run ss cs = some out) (d : IsDerivation (PHP 5 4) cs) :
    IsDerivation (PHP 5 4) out ∧ out.length = ss.length + cs.length := by
  induction ss generalizing cs with
  | nil => simp [run] at h; subst out; simp [d]
  | cons s ss ih =>
    cases hc : step s cs with
    | none => simp [run,hc] at h
    | some c =>
      simp [run,hc] at h
      obtain ⟨hd,hl⟩ := ih h (step_sound hc d)
      exact ⟨hd,by simp at hl ⊢; omega⟩

def check (ss : List Step) : Bool :=
  match run ss [] with
  | none => false
  | some cs => decide ((∅ : C) ∈ cs)

theorem certified {ss} (h : check ss = true) :
    ∃ π : List C, IsRefutation (PHP 5 4) π ∧ π.length = ss.length := by
  cases hr : run ss [] with
  | none => simp [check,hr] at h
  | some cs =>
    obtain ⟨hd,hl⟩ := run_sound hr .nil
    exact ⟨cs,⟨hd,by simpa [check,hr] using h⟩,by simpa using hl⟩

def witness : List Step := [
  .pigeon 0,
  .pigeon 1,
  .hole 0 1 0,
  .resolve 2 0 (0,0),
  .resolve 2 0 (1,0),
  .hole 0 1 1,
  .resolve 5 0 (0,1),
  .resolve 5 0 (1,1),
  .hole 0 1 2,
  .resolve 8 0 (0,2),
  .resolve 8 0 (1,2),
  .hole 0 1 3,
  .resolve 11 0 (0,3),
  .resolve 11 0 (1,3),
  .pigeon 2,
  .hole 0 2 0,
  .resolve 8 0 (0,0),
  .hole 1 2 0,
  .resolve 1 0 (1,0),
  .resolve 4 0 (2,0),
  .hole 0 2 1,
  .resolve 16 0 (0,1),
  .hole 1 2 1,
  .resolve 1 0 (1,1),
  .resolve 4 0 (2,1),
  .resolve 14 9 (0,0),
  .resolve 0 8 (1,0),
  .resolve 12 0 (2,0),
  .hole 0 2 2,
  .resolve 24 0 (0,2),
  .hole 1 2 2,
  .resolve 1 0 (1,2),
  .resolve 4 0 (2,2),
  .resolve 19 17 (0,0),
  .resolve 0 16 (1,0),
  .resolve 20 0 (2,0),
  .hole 0 2 3,
  .resolve 32 0 (0,3),
  .hole 1 2 3,
  .resolve 1 0 (1,3),
  .resolve 4 0 (2,3),
  .resolve 30 20 (0,1),
  .resolve 0 19 (1,1),
  .resolve 28 0 (2,1),
  .resolve 36 15 (0,2),
  .resolve 0 14 (1,2),
  .resolve 2 0 (2,2),
  .resolve 33 26 (0,1),
  .resolve 0 25 (1,1),
  .resolve 34 0 (2,1),
  .resolve 42 13 (0,3),
  .resolve 0 12 (1,3),
  .resolve 2 0 (2,3),
  .resolve 39 24 (0,2),
  .resolve 0 23 (1,2),
  .resolve 40 0 (2,2),
  .resolve 45 19 (0,3),
  .resolve 0 18 (1,3),
  .resolve 2 0 (2,3),
  .pigeon 3,
  .hole 0 3 0,
  .resolve 14 0 (0,0),
  .hole 1 3 0,
  .resolve 1 0 (1,0),
  .hole 2 3 0,
  .resolve 1 0 (2,0),
  .resolve 6 0 (3,0),
  .hole 0 3 1,
  .resolve 35 0 (0,1),
  .hole 1 3 1,
  .resolve 1 0 (1,1),
  .hole 2 3 1,
  .resolve 1 0 (2,1),
  .resolve 6 0 (3,1),
  .hole 0 3 2,
  .resolve 50 0 (0,2),
  .hole 1 3 2,
  .resolve 1 0 (1,2),
  .hole 2 3 2,
  .resolve 1 0 (2,2),
  .resolve 6 0 (3,2),
  .resolve 28 20 (0,0),
  .resolve 0 19 (1,0),
  .resolve 0 18 (2,0),
  .resolve 24 0 (3,0),
  .resolve 44 17 (0,1),
  .resolve 0 16 (1,1),
  .resolve 0 15 (2,1),
  .resolve 3 0 (3,1),
  .hole 0 3 3,
  .resolve 65 0 (0,3),
  .hole 1 3 3,
  .resolve 1 0 (1,3),
  .hole 2 3 3,
  .resolve 1 0 (2,3),
  .resolve 6 0 (3,3),
  .resolve 37 35 (0,0),
  .resolve 0 34 (1,0),
  .resolve 0 33 (2,0),
  .resolve 39 0 (3,0),
  .resolve 59 25 (0,2),
  .resolve 0 24 (1,2),
  .resolve 0 23 (2,2),
  .resolve 3 0 (3,2),
  .resolve 71 14 (0,3),
  .resolve 0 13 (1,3),
  .resolve 0 12 (2,3),
  .resolve 3 0 (3,3),
  .resolve 49 40 (0,1),
  .resolve 0 39 (1,1),
  .resolve 0 38 (2,1),
  .resolve 51 0 (3,1),
  .resolve 59 37 (0,2),
  .resolve 0 36 (1,2),
  .resolve 0 35 (2,2),
  .resolve 3 0 (3,2),
  .resolve 69 26 (0,3),
  .resolve 0 25 (1,3),
  .resolve 0 24 (2,3),
  .resolve 3 0 (3,3),
  .pigeon 4,
  .hole 0 4 0,
  .resolve 2 0 (0,0),
  .hole 1 4 0,
  .resolve 1 0 (1,0),
  .hole 2 4 0,
  .resolve 1 0 (2,0),
  .hole 3 4 0,
  .resolve 1 0 (3,0),
  .resolve 8 0 (4,0),
  .hole 0 4 1,
  .resolve 23 0 (0,1),
  .hole 1 4 1,
  .resolve 1 0 (1,1),
  .hole 2 4 1,
  .resolve 1 0 (2,1),
  .hole 3 4 1,
  .resolve 1 0 (3,1),
  .resolve 8 0 (4,1),
  .hole 0 4 2,
  .resolve 44 0 (0,2),
  .hole 1 4 2,
  .resolve 1 0 (1,2),
  .hole 2 4 2,
  .resolve 1 0 (2,2),
  .hole 3 4 2,
  .resolve 1 0 (3,2),
  .resolve 8 0 (4,2),
  .hole 0 4 3,
  .resolve 68 0 (0,3),
  .hole 1 4 3,
  .resolve 1 0 (1,3),
  .hole 2 4 3,
  .resolve 1 0 (2,3),
  .hole 3 4 3,
  .resolve 1 0 (3,3),
  .resolve 8 0 (4,3)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem upper_bound : ∃ π : List C, IsRefutation (PHP 5 4) π ∧ π.length = 157 := by
  apply certified (ss := witness)
  decide

end PEqualNP.Research.PHP54

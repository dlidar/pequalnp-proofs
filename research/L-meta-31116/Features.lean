import Boundary
namespace Graph31116
def prefixBits (k : Fin 6) (x : Input) : Fin 13 → Bool :=
  let a := if k.val%2=0 then x 2 || x 3 else x 3 || x 6
  let b := if k.val/2=0 then x 1 || x 4 else if k.val/2=1 then x 1 || x 7 else x 4 || x 7
  let c := (x 1 || x 4 || x 7)
  let h := a && c
  ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,a,b,c,h,!h]
def assignedRow (m : Nat) : Input := fun j => m.testBit j
def sample (k : Fin 6) (i : Fin 8) (neg : Bool) : Input :=
  let v := (([(17,16),(18,16),(36,40),(72,68),(17,3),(33,1),(65,1),(129,3),(17,16),(18,16),(36,32),(72,64),(17,3),(33,1),(65,9),(129,3),(17,16),(130,128),(36,40),(72,68),(17,3),(33,1),(65,1),(129,3),(17,16),(130,128),(36,32),(72,64),(17,3),(33,1),(65,9),(129,3),(17,16),(18,16),(36,40),(72,68),(144,128),(33,1),(65,1),(132,20),(17,16),(18,16),(36,32),(72,64),(144,128),(33,1),(65,9),(132,20)] : List (Nat × Nat)).getD (k.val*8+i.val) (0,0))
  assignedRow (if neg then v.2 else v.1)
theorem obstruction : ∀ k i,
    target (sample k i false)=true ∧ target (sample k i true)=false ∧
    ∀ j : Fin 13, j.val ≠ i.val → prefixBits k (sample k i false) j ≤ prefixBits k (sample k i true) j := by
  decide +kernel
def deleteBit (w : Fin 13 → Bool) (i : Fin 8) (j : Fin 13) :=
  if j.val=i.val then false else w j
theorem every_raw_is_needed (k : Fin 6) (D : (Fin 13 → Bool) → Bool) (hm : Monotone D)
    (ok : ∀ x,D (prefixBits k x)=target x) (i : Fin 8) :
    ∃ w, D w=true ∧ D (deleteBit w i)=false := by
  obtain ⟨ht,hf,h⟩ := obstruction k i
  refine ⟨prefixBits k (sample k i false),(ok _).trans ht,?_⟩
  have le : deleteBit (prefixBits k (sample k i false)) i ≤ prefixBits k (sample k i true) := by
    intro j; by_cases c : j.val=i.val
    · simp [deleteBit,c]
    · simpa [deleteBit,c] using h j c
  have z := hm le; rw [ok,hf] at z
  exact le_antisymm z (Bool.false_le _)
end Graph31116

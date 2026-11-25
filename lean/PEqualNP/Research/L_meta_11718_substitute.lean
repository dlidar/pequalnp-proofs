import PEqualNP.Research.L_meta_11718_repair

namespace PEqualNP.Research.InverterSubstitution
open PEqualNP.CircuitLowerBounds PEqualNP.Research.SingleInverter
open PEqualNP.Research.InverterCircuit PEqualNP.Research.SevenVertexInverter PEqualNP.Research.InverterRepair

def replacementGate (join : Bool) (a : Fin 7) : Gate :=
  if join then (if a = 0 then ⟨.or,[4,6]⟩ else ⟨.or,[0,1]⟩) else ⟨.and,[]⟩

def eligible (z : Bool) (a b : Fin 7) := if z then exceptional a b else linked a b

theorem fixed_compatible : ∀ a b : Fin 7, ∀ z : Bool, eligible z a b = true →
    compatible (pairSig z a b) (fun x => stepValue (replacementGate z a) (input x)) = true := by
  decide +kernel

theorem replacement_shape (z : Bool) (a : Fin 7) :
    let g := replacementGate z a
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < 7 := by
  cases z <;> by_cases h : a = 0 <;> simp [replacementGate,h]

theorem old_wire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc,List.getD_append _ _ _ _ (by rw [run_length]; omega),ih]

theorem raw_gate_preserved (g : Gate) (w : List Bool) (gs : List Gate)
    (bound : ∀ i ∈ g.inputs, i < w.length) :
    stepValue g (run gs w) = stepValue g w := by
  unfold stepValue
  congr 1
  exact List.map_congr_left (fun i hi => old_wire gs w i (bound i hi))

theorem preserve_size (pre post : List Gate) (args : List ℕ) (o : ℕ) (a b : Fin 7) (z : Bool)
    (hp : binaryMono pre) (ht : binaryMono post)
    (fan : ∀ g ∈ pre ++ post, g.inputs.length ≤ 2)
    (matchCut : ∀ x : Row (Fin 7), signal pre args x = pairSig z a b x)
    (good : eligible z a b = true)
    (fits : ∀ x : Row (Fin 7), out pre post args o x = graph x) :
    replacement (substitute pre post ⟨.not,args⟩ o) := by
  let g := replacementGate z a
  have shape := replacement_shape z a
  have mask := (compatible_iff _ _).mp (fixed_compatible a b z good)
  have repaired := boundary_repair pre post args o 7 graph g hp ht shape.1 fits (by
    intro x hx
    rw [matchCut,raw_gate_preserved g _ pre (by simpa [input] using shape.2.2)]
    exact mask x hx)
  refine ⟨pre ++ g :: post,o,?_,by simp [substitute],?_⟩
  · intro t hm
    rcases List.mem_append.mp hm with lhs | rhs
    · exact ⟨hp t lhs,fan t (List.mem_append_left _ lhs)⟩
    · rcases List.mem_cons.mp rhs with e | hr
      · subst t
        exact ⟨shape.1,shape.2.1⟩
      · exact ⟨ht t hr,fan t (List.mem_append_right _ hr)⟩
  · intro x
    have enc : input (rowOf x) = List.ofFn x := by simp [input,rowOf]
    simpa only [substitute, enc, graph_posted] using repaired (rowOf x)

end PEqualNP.Research.InverterSubstitution

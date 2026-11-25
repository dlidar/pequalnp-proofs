import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Research.L_meta_4675_star_networks

namespace PEqualNP.Research.SevenAdvice
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.StarNetworks

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

def col (j : Fin 7) (d : ℕ) : Fin 42 := Fin.ofNat 42 (21+(3*j.val+d)%21)
def enc (x : Fin 42 → Bool) : List Bool :=
  (List.ofFn x ++ List.ofFn fun j : Fin 7 => x (col j 5) || x (col j 17)) ++
    List.ofFn fun j : Fin 7 => x (col j 5) || x (col j 17) || x (col j 20)
def edge (u v : Fin 42) := u.val < 21 ∧ 21 ≤ v.val ∧
  (v.val+21-u.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
instance (u v) : Decidable (edge u v) := by unfold edge; infer_instance
def target (x : Fin 42 → Bool) : Prop := ∃ u v, edge u v ∧ x u = true ∧ x v = true

-- Symbolic wire values are positive DNFs in the original 42 variables.
abbrev Poly := List (List (Fin 42))
def truth (x : Fin 42 → Bool) (P : Poly) := P.any fun t => t.all x
def product (P Q : Poly) : Poly := P.flatMap fun t => Q.map fun s => t ++ s
theorem truth_product (x : Fin 42 → Bool) (P Q : Poly) :
    truth x (product P Q) = (truth x P && truth x Q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [truth,product,List.any_eq_true,List.mem_flatMap,List.mem_map,Bool.and_eq_true]
  constructor
  · rintro ⟨_,⟨t,ht,s,hs,rfl⟩,val⟩
    rw [List.all_append,Bool.and_eq_true] at val
    obtain ⟨vt,vs⟩ := val
    exact ⟨⟨t,ht,vt⟩,s,hs,vs⟩
  · rintro ⟨⟨t,ht,vt⟩,s,hs,vs⟩
    exact ⟨_,⟨t,ht,s,hs,rfl⟩,by simp [vt,vs]⟩

def sym (w : List Poly) (g : Gate) : Poly :=
  let a := w.getD (g.inputs.getD 0 0) []
  let b := w.getD (g.inputs.getD 1 0) []
  if g.op = .and then product a b else a ++ b
def legal (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]
private theorem read_map (x : Fin 42 → Bool) (w : List Poly) (i : ℕ) :
    (w.map (truth x)).getD i false = truth x (w.getD i []) := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]; rfl

theorem symbolic_wires (x : Fin 42 → Bool) (gs : List Gate) (ok : ∀ g ∈ gs, legal g) (xs : List Poly) :
      (gs.foldl (fun z g => z ++ [sym z g]) xs).map (truth x) =
        (Circuit.mk gs 0).wires (xs.map (truth x)) := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (fun t ht => ok t (by simp [ht])),List.map_append,List.map_singleton]
      change (Circuit.mk gs 0).wires _ = (Circuit.mk gs 0).wires (_ ++ [_])
      congr 2
      obtain ⟨op,a,b,ab⟩ := ok g List.mem_cons_self
      have r0 : [a,b].getD 0 0 = a := rfl
      have r1 : [a,b].getD 1 0 = b := rfl
      have join (P Q : Poly) : truth x (P++Q) = (truth x P || truth x Q) := List.any_append
      rcases op with op | op <;>
        simp only [sym,ab,op,r0,r1,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
          List.any_cons,List.any_nil,Bool.and_true,Bool.or_false,read_map,ite_true,truth_product,join,
          reduceCtorEq,ite_false,id_eq]

theorem sym_sound (C : Circuit) (h : ∀ g ∈ C.gates, legal g) (w : List Poly) (x : Fin 42 → Bool) :
    C.eval (w.map (truth x)) =
      truth x ((C.gates.foldl (fun z g => z ++ [sym z g]) w).getD C.output []) := by
  change (C.wires (w.map (truth x))).getD C.output false = _
  rw [← show (C.gates.foldl (fun z g => z ++ [sym z g]) w).map (truth x) = C.wires (w.map (truth x)) from symbolic_wires x C.gates h w,read_map]

def inputs : List Poly := (List.ofFn (fun i : Fin 42 => [[i]]) ++
    List.ofFn (fun j : Fin 7 => [[col j 5],[col j 17]])) ++
    List.ofFn (fun j : Fin 7 => [[col j 5],[col j 17],[col j 20]])
theorem inputs_ok (x : Fin 42 → Bool) : inputs.map (truth x) = enc x := by
  simp [inputs,enc,truth,Bool.or_assoc]

def reference : Circuit := ⟨[⟨.or,[21,28]⟩,
  ⟨.or,[56,49]⟩,
  ⟨.and,[0,57]⟩,
  ⟨.or,[22,27]⟩,
  ⟨.or,[59,29]⟩,
  ⟨.or,[60,39]⟩,
  ⟨.or,[61,21]⟩,
  ⟨.and,[1,62]⟩,
  ⟨.or,[23,28]⟩,
  ⟨.or,[64,30]⟩,
  ⟨.or,[65,40]⟩,
  ⟨.or,[66,22]⟩,
  ⟨.and,[2,67]⟩,
  ⟨.or,[24,31]⟩,
  ⟨.or,[69,50]⟩,
  ⟨.and,[3,70]⟩,
  ⟨.or,[25,30]⟩,
  ⟨.or,[72,32]⟩,
  ⟨.or,[73,21]⟩,
  ⟨.or,[74,24]⟩,
  ⟨.and,[4,75]⟩,
  ⟨.or,[26,31]⟩,
  ⟨.or,[77,33]⟩,
  ⟨.or,[78,22]⟩,
  ⟨.or,[79,25]⟩,
  ⟨.and,[5,80]⟩,
  ⟨.or,[27,34]⟩,
  ⟨.or,[82,51]⟩,
  ⟨.and,[6,83]⟩,
  ⟨.or,[28,33]⟩,
  ⟨.or,[85,35]⟩,
  ⟨.or,[86,24]⟩,
  ⟨.or,[87,27]⟩,
  ⟨.and,[7,88]⟩,
  ⟨.or,[29,34]⟩,
  ⟨.or,[90,36]⟩,
  ⟨.or,[91,25]⟩,
  ⟨.or,[92,28]⟩,
  ⟨.and,[8,93]⟩,
  ⟨.or,[30,37]⟩,
  ⟨.or,[95,52]⟩,
  ⟨.and,[9,96]⟩,
  ⟨.or,[31,36]⟩,
  ⟨.or,[98,38]⟩,
  ⟨.or,[99,27]⟩,
  ⟨.or,[100,30]⟩,
  ⟨.and,[10,101]⟩,
  ⟨.or,[32,37]⟩,
  ⟨.or,[103,39]⟩,
  ⟨.or,[104,28]⟩,
  ⟨.or,[105,31]⟩,
  ⟨.and,[11,106]⟩,
  ⟨.or,[33,40]⟩,
  ⟨.or,[108,53]⟩,
  ⟨.and,[12,109]⟩,
  ⟨.or,[34,39]⟩,
  ⟨.or,[111,41]⟩,
  ⟨.or,[112,30]⟩,
  ⟨.or,[113,33]⟩,
  ⟨.and,[13,114]⟩,
  ⟨.or,[35,40]⟩,
  ⟨.or,[116,21]⟩,
  ⟨.or,[117,31]⟩,
  ⟨.or,[118,34]⟩,
  ⟨.and,[14,119]⟩,
  ⟨.or,[36,22]⟩,
  ⟨.or,[121,54]⟩,
  ⟨.and,[15,122]⟩,
  ⟨.or,[37,21]⟩,
  ⟨.or,[124,23]⟩,
  ⟨.or,[125,33]⟩,
  ⟨.or,[126,36]⟩,
  ⟨.and,[16,127]⟩,
  ⟨.or,[38,22]⟩,
  ⟨.or,[129,24]⟩,
  ⟨.or,[130,34]⟩,
  ⟨.or,[131,37]⟩,
  ⟨.and,[17,132]⟩,
  ⟨.or,[39,25]⟩,
  ⟨.or,[134,55]⟩,
  ⟨.and,[18,135]⟩,
  ⟨.or,[40,24]⟩,
  ⟨.or,[137,26]⟩,
  ⟨.or,[138,36]⟩,
  ⟨.or,[139,39]⟩,
  ⟨.and,[19,140]⟩,
  ⟨.or,[41,25]⟩,
  ⟨.or,[142,27]⟩,
  ⟨.or,[143,37]⟩,
  ⟨.or,[144,40]⟩,
  ⟨.and,[20,145]⟩,
  ⟨.or,[58,63]⟩,
  ⟨.or,[147,68]⟩,
  ⟨.or,[148,71]⟩,
  ⟨.or,[149,76]⟩,
  ⟨.or,[150,81]⟩,
  ⟨.or,[151,84]⟩,
  ⟨.or,[152,89]⟩,
  ⟨.or,[153,94]⟩,
  ⟨.or,[154,97]⟩,
  ⟨.or,[155,102]⟩,
  ⟨.or,[156,107]⟩,
  ⟨.or,[157,110]⟩,
  ⟨.or,[158,115]⟩,
  ⟨.or,[159,120]⟩,
  ⟨.or,[160,123]⟩,
  ⟨.or,[161,128]⟩,
  ⟨.or,[162,133]⟩,
  ⟨.or,[163,136]⟩,
  ⟨.or,[164,141]⟩,
  ⟨.or,[165,146]⟩],166⟩
def form := (reference.gates.foldl (fun z g => z ++ [sym z g]) inputs).getD reference.output []
theorem reference_size : reference.size = 111 := rfl
theorem reference_legal : ∀ g ∈ reference.gates, legal g := by
  have : ∀ g ∈ reference.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs = [g.inputs.getD 0 0,g.inputs.getD 1 0] := by decide +kernel
  intro g hg
  exact ⟨(this _ hg).1,_,_,(this _ hg).2⟩
theorem reference_mono : Monotone2 reference := by
  intro g hg
  obtain ⟨op,a,b,h⟩ := reference_legal g hg
  exact ⟨op,by simp [h]⟩
theorem exact_monomials : (∀ t ∈ form, ∃ u v, edge u v ∧ t = [u,v]) ∧
    ∀ u v, edge u v → [u,v] ∈ form := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 6000000 in decide +kernel
theorem reference_exact (x : Fin 42 → Bool) : reference.eval (enc x) = true ↔ target x := by
  rw [← inputs_ok,sym_sound reference reference_legal]
  change truth x form = true ↔ _
  simp only [truth,List.any_eq_true]
  constructor
  · rintro ⟨t,ht,val⟩
    obtain ⟨u,v,e,rfl⟩ := exact_monomials.1 t ht
    simpa using (show target x from ⟨u,v,e,by simpa using (List.all_eq_true.mp val u (by simp)),by simpa using (List.all_eq_true.mp val v (by simp))⟩)
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨[u,v],exact_monomials.2 u v e,by simp [hu,hv]⟩

def adviceGates : List Gate :=
  (List.ofFn fun j : Fin 7 => (⟨.or,[(col j 5).val,(col j 17).val]⟩ : Gate)) ++
    List.ofFn fun j : Fin 7 => (⟨.or,[42+j.val,(col j 20).val]⟩ : Gate)
def pins := List.ofFn (fun i : Fin 42 => ([[i]] : Poly))
theorem prefix_cert : adviceGates.foldl (fun z g => z++[sym z g]) pins = inputs := by decide +kernel
theorem prefix_size : adviceGates.length = 14 := by decide
theorem prefix_legal : ∀ g ∈ adviceGates, legal g := by
  intro g hg
  simp only [adviceGates, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ⟨i,rfl⟩|⟨i,rfl⟩ <;> exact ⟨Or.inr rfl,_,_,rfl⟩
theorem prefix_correct (x : Fin 42 → Bool) : (Circuit.mk adviceGates 0).wires (List.ofFn x) = enc x := by
  have t := symbolic_wires x adviceGates prefix_legal pins
  rw [prefix_cert,inputs_ok] at t
  simpa [pins, truth] using t.symm

def ordinary (C : Circuit) : Circuit := ⟨adviceGates ++ C.gates,C.output⟩
theorem ordinary_size (C : Circuit) : (ordinary C).size = 14+C.size := by simp [ordinary,Circuit.size,prefix_size]
theorem ordinary_mono (C : Circuit) (h : Monotone2 C) : Monotone2 (ordinary C) := by
  intro g hg
  rcases List.mem_append.mp hg with pre|rest
  · obtain ⟨op,a,b,eq⟩ := prefix_legal g pre
    exact ⟨op,by simp [eq]⟩
  · exact h _ rest
theorem ordinary_eval (C : Circuit) (x : Fin 42 → Bool) :
    (ordinary C).eval (List.ofFn x) = C.eval (enc x) := by
  unfold Circuit.eval Circuit.wires ordinary
  simp only [List.foldl_append]
  rw [← prefix_correct x]
  rfl

def E : Finset (Fin 21 × Fin 21) := univ.filter fun e =>
  (e.2.val+42-e.1.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
theorem cardinality : E.card = 105 := by decide +kernel
theorem thin : fourFree E := by
  let neigh (a b : Fin 21) := (b.val+42-a.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
  have bound : ∀ a a' : Fin 21, a ≠ a' → (univ.filter (fun b => neigh a b ∧ neigh a' b)).card ≤ 1 := by
    dsimp only [neigh]
    set_option maxRecDepth 32768 in
    set_option maxHeartbeats 8000000 in decide +kernel
  intro a a' b b' haa hbb h
  simp only [E,mem_filter,mem_univ,true_and] at h
  apply hbb
  apply Finset.card_le_one.mp (bound a a' haa)
  · exact mem_filter.mpr ⟨mem_univ _,h.1,h.2.2.1⟩
  · exact mem_filter.mpr ⟨mem_univ _,h.2.1,h.2.2.2⟩

theorem cover_size (S : Finset (Fin 42)) (h : ∀ a b, (a,b) ∈ E →
    Fin.castAdd 21 a ∈ S ∨ Fin.natAdd 21 b ∈ S) : 21 ≤ S.card := by
  have diag : ∀ i : Fin 21, (i,i) ∈ E := by decide +kernel
  let f (i : Fin 21) := if Fin.castAdd 21 i ∈ S then Fin.castAdd 21 i else Fin.natAdd 21 i
  have inside : univ.image f ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    dsimp [f]; split
    · assumption
    · exact (h _ _ (diag i)).resolve_left (by assumption)
  have inj : Function.Injective f := by
    intro i j eq
    have e := congrArg Fin.val eq
    by_cases hi : Fin.castAdd 21 i ∈ S <;> by_cases hj : Fin.castAdd 21 j ∈ S <;>
      simp only [f,hi,hj,ite_true,ite_false,Fin.val_castAdd,Fin.val_natAdd] at e <;>
      apply Fin.ext <;> have := i.isLt <;> have := j.isLt <;> omega
  simpa [card_image_of_injective _ inj] using card_le_card inside

/-- The two banks of seven cached unions are free for the consumer. Any
shared-OR network forming rectangles that cover exactly the incidences
still pays at least 111 consumer gates. -/
theorem cached_rectangle_lower (s m : ℕ) (W : ℕ → Finset (Vertex 21 21))
    (raw : ∀ i < 42, (W i).card ≤ 1)
    (pairs : ∀ j : Fin 7, W (42+j.val) = W (col j 5).val ∪ W (col j 17).val)
    (triples : ∀ j : Fin 7, W (49+j.val) = W (42+j.val) ∪ W (col j 20).val)
    (consumer : ∀ j < s, ∃ a b : ℕ, a < 56+j ∧ b < 56+j ∧ W (56+j) = W a ∪ W b)
    (x y : Fin m → ℕ) (valid : ∀ j, x j < 56+s ∧ y j < 56+s)
    (used : ∀ j, (W (x j)).Nonempty ∧ (W (y j)).Nonempty)
    (sound : ∀ j u, u ∈ W (x j) → ∀ v ∈ W (y j), adjacent E u v)
    (complete : ∀ e ∈ E, ∃ j u v, u ∈ W (x j) ∧ v ∈ W (y j) ∧ decode (u,v) = some e) :
    111 ≤ s+m+(m-1) := by
  have lb := rectangle_network_bound 21 21 42 (14+s) m E thin W raw (by
    intro j hj
    by_cases lo : j < 7
    · let t : Fin 7 := ⟨j,lo⟩
      exact ⟨_,_,by have := (col t 5).isLt; omega,by have := (col t 17).isLt; omega,pairs t⟩
    by_cases mid : j < 14
    · let t : Fin 7 := ⟨j-7,by omega⟩
      have eq : 42+j=49+t.val := by dsimp [t]; omega
      rw [eq]
      exact ⟨_,_,by omega,by have := (col t 20).isLt; omega,triples t⟩
    have eq : 42+j=56+(j-14) := by omega
    rw [eq]; exact consumer _ (by omega)) x y (by
      intro j; obtain ⟨a,b⟩ := valid j; constructor <;> omega) used sound complete
  obtain ⟨S,cov,bound⟩ := lb
  have := cover_size S cov
  rw [cardinality] at bound
  omega

theorem sufficient_lower (h : ∀ D : Circuit, Monotone2 D →
    (∀ x, D.eval (List.ofFn x) = true ↔ target x) → 125 ≤ D.size) :
    ¬ (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (110 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.eval               (have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));               (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) =             Bool.true ↔           ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true) := by
  rintro ⟨C,mono,size,ok⟩
  have lb := h (ordinary C) (ordinary_mono C mono) (by
    intro x; rw [ordinary_eval]; exact ok x)
  rw [ordinary_size] at lb
  omega
end PEqualNP.Research.SevenAdvice

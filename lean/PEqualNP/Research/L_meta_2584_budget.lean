import PEqualNP.Defs

namespace PEqualNP.Research.ReadTwoBudget
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.TopForm
abbrev Bag := List (List ℕ)
abbrev State := Fin 3 → Fin 3 → Bool

def fits (v : List ℕ) (i j : Fin 3) : Bool :=
  decide (v.getD 0 3 ≤ i.val ∧ v.getD 1 3 ≤ j.val)
def encode (A : Bag) : State := fun i j => A.any fun v => fits v i j
def zero : State := fun _ _ => false
def add (a b : State) : State := fun i j => a i j || b i j
def mul (a b : State) : State := fun i j => decide <| ∃ u v x y : Fin 3,
  u.val+x.val ≤ i.val ∧ v.val+y.val ≤ j.val ∧ a u v = true ∧ b x y = true

lemma ins_mem (A : Bag) (a v : List ℕ) : v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  by_cases h : a ∈ A <;> simp [insertNew,h] <;> aesop
lemma union_mem (A B : Bag) (v : List ℕ) : v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih,ins_mem,or_assoc]
lemma times_mem (A B : Bag) (v : List ℕ) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, capAdd 2 u w = v := by
  simp [andStep,union_mem,List.mem_flatMap,List.mem_map]

theorem encode_union (A B : Bag) : encode (B.foldl insertNew A) = add (encode A) (encode B) := by
  funext i j; apply Bool.eq_iff_iff.mpr
  simp only [encode, add,List.any_eq_true,union_mem,Bool.or_eq_true]
  aesop

lemma cap_fits (v w : List ℕ) (i j : Fin 3) :
    fits (capAdd 2 v w) i j = true ↔
      v.getD 0 3 + w.getD 0 3 ≤ i.val ∧ v.getD 1 3 + w.getD 1 3 ≤ j.val := by
  have hi := i.isLt; have hj := j.isLt
  rcases v with _ | ⟨a,_ | ⟨b,t⟩⟩ <;> rcases w with _ | ⟨c,_ | ⟨d,s⟩⟩ <;>
    simp [fits,capAdd,List.getD,List.zipWith] <;> omega

theorem encode_times (A B : Bag) : encode (andStep 2 A B) = mul (encode A) (encode B) := by
  funext i j; apply Bool.eq_iff_iff.mpr
  simp only [encode,List.any_eq_true,times_mem,mul,decide_eq_true_eq]
  constructor
  · rintro ⟨_,⟨a,ha,b,hb,rfl⟩,h⟩
    obtain ⟨h1,h2⟩ := (cap_fits a b i j).mp h
    have hi := i.isLt; have hj := j.isLt
    exact ⟨⟨a.getD 0 3, by omega⟩,⟨a.getD 1 3,by omega⟩,
      ⟨b.getD 0 3,by omega⟩,⟨b.getD 1 3,by omega⟩,h1,h2,
      ⟨a,ha,by simp [fits]⟩,⟨b,hb,by simp [fits]⟩⟩
  · rintro ⟨u,v,x,y,h1,h2,⟨a,ha,fa⟩,⟨b,hb,fb⟩⟩
    refine ⟨_,⟨a,ha,b,hb,rfl⟩,(cap_fits _ _ _ _).mpr ?_⟩
    simp only [fits,decide_eq_true_eq] at fa fb
    constructor <;> omega

def fastStep (W : List State) (g : Gate) : State :=
  let a := W.getD (g.inputs.getD 0 0) zero
  let b := W.getD (g.inputs.getD 1 0) zero
  match g.op with
  | .or => add a b | .and => mul a b | _ => zero

def fastWires (C : Circuit) (n a b : ℕ) : List State :=
  C.gates.foldl (fun W g => W ++ [fastStep W g])
    ((List.range n).map fun i => encode (leafVectors [a,b] 2 i))

def originalStep (W : List Bag) (g : Gate) : Bag :=
  let ins := g.inputs.map fun i => W.getD i []
  match g.op with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [[0,0]]
  | _ => []

lemma default_wire (W : List Bag) (i : ℕ) : (W.map encode).getD i zero = encode (W.getD i []) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases W[i]? <;> rfl

lemma bottom_add (a : State) : add (encode []) a = a := by funext i j; rfl

lemma mono_encode (A : Bag) (i j x y : Fin 3) (hx : i ≤ x) (hy : j ≤ y) :
    encode A i j = true → encode A x y = true := by
  simp only [encode,List.any_eq_true,fits,decide_eq_true_eq]
  rintro ⟨v,hv,h,k⟩; exact ⟨v,hv,h.trans hx,k.trans hy⟩

lemma identity_mul (A : Bag) : mul (encode [[0,0]]) (encode A) = encode A := by
  funext i j; apply Bool.eq_iff_iff.mpr
  simp only [mul,decide_eq_true_eq]
  constructor
  · rintro ⟨u,v,x,y,h1,h2,-,h⟩
    exact mono_encode A x y i j (show x.val ≤ i.val by omega) (show y.val ≤ j.val by omega) h
  · intro h; exact ⟨0,0,i,j,by simp,by simp,by simp [encode,fits,List.getD],h⟩

lemma step_eq (W : List Bag) (g : Gate) (arity : g.inputs.length = 2) :
    encode (originalStep W g) = fastStep (W.map encode) g := by
  obtain ⟨a,b,e⟩ := List.length_eq_two.mp arity
  cases h : g.op <;>
    simp only [originalStep,fastStep,h,e,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
      encode_union,encode_times,bottom_add,identity_mul] <;>
    first | rfl | simp only [List.getD_cons_zero,List.getD_cons_succ,default_wire]

theorem all_wires (C : Circuit) {n : ℕ} (h : IsAO2 n C) (a b : ℕ) :
    (readVectors C n [a,b] 2).map encode = fastWires C n a b := by
  have fold (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2) (W : List Bag) :
      (gs.foldl (fun w g => w ++ [originalStep w g]) W).map encode =
      gs.foldl (fun w g => w ++ [fastStep w g]) (W.map encode) := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (fun g hg => arity _ (List.mem_cons_of_mem _ hg))]
      simp only [List.map_append,List.map_singleton,step_eq _ _ (arity g (by simp))]
  let W := (List.range n).map (leafVectors [a,b] 2)
  have eqR : readVectors C n [a,b] 2 = C.gates.foldl (fun w g => w ++ [originalStep w g]) W := by
    unfold readVectors
    congr 1
  rw [eqR,fold _ h.2.2]
  simp only [W,List.map_map,Function.comp_def,fastWires]


def Well (A : Bag) : Prop := ∀ v ∈ A, v.length = 2
lemma well_times (A B : Bag) (ha : Well A) (hb : Well B) : Well (andStep 2 A B) := by
  intro v hv; obtain ⟨u,hu,w,hw,rfl⟩ := (times_mem A B v).mp hv
  simp [capAdd,ha u hu,hb w hw]
lemma well_union (A B : Bag) (ha : Well A) (hb : Well B) : Well (B.foldl insertNew A) := by
  intro v hv; exact ((union_mem A B v).mp hv).elim (ha v) (hb v)
lemma well_get (W : List Bag) (h : ∀ A ∈ W, Well A) (i : ℕ) : Well (W.getD i []) := by
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; simp [Well]

theorem well_wires (C : Circuit) {n : ℕ} (h : IsAO2 n C) (a b : ℕ) :
    ∀ W ∈ readVectors C n [a,b] 2, Well W := by
  have fold (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2)
      (W : List Bag) (hh : ∀ A ∈ W, Well A) :
      ∀ A ∈ gs.foldl (fun w g => w ++ [originalStep w g]) W, Well A := by
    induction gs generalizing W with
    | nil => exact hh
    | cons g gs ih =>
      apply ih (fun g hg => arity _ (List.mem_cons_of_mem _ hg))
      intro A ha; simp only [List.mem_append,List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hh _ ha
      · obtain ⟨a,b,e⟩ := List.length_eq_two.mp (arity g (by simp))
        cases hop : g.op <;> simp only [originalStep,hop,e,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil]
        · exact well_times _ _ (well_times _ _ (by simp [Well]) (well_get _ hh _)) (well_get _ hh _)
        · exact well_union _ _ (well_union _ _ (by simp [Well]) (well_get _ hh _)) (well_get _ hh _)
        all_goals simp [Well]
  apply fold C.gates h.2.2
  intro A ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  by_cases hi : i ∈ [a,b] <;> simp [leafVectors,hi,Well]

theorem correct (C : Circuit) {n : ℕ} (h : IsAO2 n C) (a b : ℕ) :
    readsAtMost C n [a,b] 2 = ((fastWires C n a b).getD C.output zero) 2 2 := by
  rw [← all_wires C h,default_wire]
  unfold readsAtMost encode
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  have hw := well_get _ (well_wires C h a b) C.output
  have eqv (v : List ℕ) (hv : v ∈ (readVectors C n [a,b] 2).getD C.output []) :
      (v.all fun a => decide (a ≤ 2)) = fits v 2 2 := by
    obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp (hw v hv)
    simp [fits,List.getD]
  constructor <;> rintro ⟨v,hv,p⟩ <;> exact ⟨v,hv,by simpa only [eqv v hv] using p⟩

#print axioms correct
end PEqualNP.Research.ReadTwoBudget

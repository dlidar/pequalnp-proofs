import PEqualNP.Research.SixCofactors3321
import PEqualNP.Research.Residual3321

namespace PEqualNP.Research.Transport3321
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.GateCuts3321 PEqualNP.Research.SixCofactors3321
open PEqualNP.Research.ForestNormal3321 PEqualNP.Research.Residual3321

noncomputable def value {p l} (E : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) : Bool :=
  by classical exact decide (Target E x)

theorem value_true {p l} (E : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) :
    value E x = true ↔ Target E x := by classical simp [value]

def Bounds {p l} (E : Finset (Fin p × Fin l)) (lo hi : ℕ) : Prop :=
  Lower (value E) lo ∧ ∃ (P : Finset (Fin p)) (L : Finset (Fin l)),
    (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧ E.card + P.card + L.card - 1 ≤ hi

theorem exact_normal {N s} {E : Finset (Fin N × Fin N)} (h : Bounds E s s)
    (C : Circuit) (fan : FanInTwo C) (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target E z) :
    Posted E C.size := by
  obtain ⟨low,P,L,cov,k⟩ := h
  have hc : HasCircuitSize (N+N) (value E) C.size :=
    ⟨C,fan,le_rfl,fun z => Bool.eq_iff_iff.mpr ((ev z).trans (value_true E z).symm)⟩
  obtain ⟨D,ao,sz,out,safe⟩ := compile_cover E P L cov
  exact strong_to_posted _ _ ⟨D,ao,sz.trans (k.trans (low _ hc)),out,safe⟩

theorem pullback {p l q r k} {G : Finset (Fin p × Fin l)} {E : Finset (Fin q × Fin r)}
    (h : Lower (value G) k) (undo : Fin (q+r) → Fin (p+l))
    (transport : ∀ x, Target E (x ∘ undo) ↔ Target G x) : Lower (value E) k := by
  intro s hs
  have hc := Helpers.PermInputs.relabel_size undo _ _ hs
  have e : (fun x => value E (x ∘ undo)) = value G := by
    funext x;apply Bool.eq_iff_iff.mpr
    rw [value_true,value_true];exact transport x
  rw [e] at hc;exact h s hc

theorem embedding {n p l lo hi} [Nonempty (Fin n)] (G : Finset (Fin n × Fin n))
    (left : Fin n ↪ Fin p) (right : Fin n ↪ Fin l) (h : Bounds G lo hi) :
    Bounds (G.image fun e => (left e.1,right e.2)) lo hi := by
  classical
  let E := G.image fun e => (left e.1,right e.2)
  let undo : Fin (p+l) → Fin (n+n) := Fin.addCases
      (fun i => Fin.castAdd n (Function.invFun left i)) (fun j => Fin.natAdd n (Function.invFun right j))
  have undo_left (i) : undo (Fin.castAdd l (left i)) = Fin.castAdd n i := by
    simp [undo,Function.leftInverse_invFun left.injective i]
  have undo_right (j) : undo (Fin.natAdd p (right j)) = Fin.natAdd n j := by
    simp [undo,Function.leftInverse_invFun right.injective j]
  have transport (x : Fin (n+n) → Bool) : Target E (x ∘ undo) ↔ Target G x := by
    constructor
    · rintro ⟨p,l,h,a,b⟩
      obtain ⟨⟨i,j⟩,he,eq⟩ := mem_image.mp h
      cases eq
      exact ⟨i,j,he,by simpa only [Function.comp_apply,undo_left] using a,by simpa only [Function.comp_apply,undo_right] using b⟩
    · rintro ⟨i,j,he,a,b⟩
      exact ⟨left i,right j,mem_image.mpr ⟨(i,j),he,rfl⟩,by simpa only [Function.comp_apply,undo_left] using a,
         by simpa only [Function.comp_apply,undo_right] using b⟩

  refine ⟨pullback h.1 undo transport,?_⟩
  obtain ⟨P,L,cov,budget⟩ := h.2
  refine ⟨P.image left,L.image right,?_,?_⟩
  · rintro _ he
    obtain ⟨e,old,rfl⟩ := mem_image.mp he
    exact (cov e old).imp (fun hp => mem_image.mpr ⟨_,hp,rfl⟩) (fun hl => mem_image.mpr ⟨_,hl,rfl⟩)
  · have ec : E.card ≤ G.card := card_image_le
    have pc : (P.image left).card ≤ P.card := card_image_le
    have lc : (L.image right).card ≤ L.card := card_image_le
    change E.card + _ + _ - 1 ≤ hi
    omega

theorem transpose {p l lo hi} (G : Finset (Fin p × Fin l)) (h : Bounds G lo hi) :
    Bounds (G.image Prod.swap) lo hi := by
  let undo : Fin (l+p) → Fin (p+l) := Fin.addCases (Fin.natAdd p) (Fin.castAdd l)
  have swap_inputs (x : Fin (p+l) → Bool) :
      Target (G.image Prod.swap) (x ∘ undo) ↔ Target G x := by
    constructor
    · rintro ⟨j,i,he,a,b⟩
      obtain ⟨⟨u,v⟩,edge,eq⟩ := mem_image.mp he
      cases eq
      exact ⟨u,v,edge,by simpa [undo] using b,by simpa [undo] using a⟩
    · rintro ⟨i,j,he,a,b⟩
      exact ⟨j,i,mem_image.mpr ⟨(i,j),he,rfl⟩,by simpa [undo] using b,by simpa [undo] using a⟩
  refine ⟨pullback h.1 undo swap_inputs,?_⟩
  obtain ⟨P,L,cov,budget⟩ := h.2
  refine ⟨L,P,?_,?_⟩
  · rintro _ he
    obtain ⟨⟨i,j⟩,old,rfl⟩ := mem_image.mp he
    exact (cov _ old).symm
  · have ec : (G.image Prod.swap).card ≤ G.card := card_image_le
    omega

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

def incidence862 : Finset (Fin 4 × Fin 4) := {(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)}
theorem bounds_862 : Bounds incidence862 9 9 := by
  have spec : ∀ x, graph862 x = true ↔ Target incidence862 x := by unfold Target;decide +kernel
  have idf : value incidence862 = graph862 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph862,{0,1,2},∅,by decide,by decide⟩

def incidence4958 : Finset (Fin 4 × Fin 4) := {(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0)}
theorem bounds_4958 : Bounds incidence4958 10 11 := by
  have spec : ∀ x, graph4958 x = true ↔ Target incidence4958 x := by unfold Target;decide +kernel
  have idf : value incidence4958 = graph4958 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph4958,{0,1,2,3},∅,by decide,by decide⟩

def incidence4973 : Finset (Fin 4 × Fin 4) := {(0,0),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)}
theorem bounds_4973 : Bounds incidence4973 10 11 := by
  have spec : ∀ x, graph4973 x = true ↔ Target incidence4973 x := by unfold Target;decide +kernel
  have idf : value incidence4973 = graph4973 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph4973,{0,1,2,3},∅,by decide,by decide⟩

def incidence5804 : Finset (Fin 4 × Fin 4) := {(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0)}
theorem bounds_5804 : Bounds incidence5804 10 10 := by
  have spec : ∀ x, graph5804 x = true ↔ Target incidence5804 x := by unfold Target;decide +kernel
  have idf : value incidence5804 = graph5804 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph5804,{0,1,2,3},∅,by decide,by decide⟩

def incidence5805 : Finset (Fin 4 × Fin 4) := {(0,0),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0)}
theorem bounds_5805 : Bounds incidence5805 11 11 := by
  have spec : ∀ x, graph5805 x = true ↔ Target incidence5805 x := by unfold Target;decide +kernel
  have idf : value incidence5805 = graph5805 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph5805,{0,1,2,3},∅,by decide,by decide⟩

def incidence13726 : Finset (Fin 4 × Fin 4) := {(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(3,0),(3,1)}
theorem bounds_13726 : Bounds incidence13726 10 12 := by
  have spec : ∀ x, graph13726 x = true ↔ Target incidence13726 x := by unfold Target;decide +kernel
  have idf : value incidence13726 = graph13726 := by
    funext x;exact Bool.eq_iff_iff.mpr ((value_true _ _).trans (spec x).symm)
  exact ⟨by rw [idf];exact lower_graph13726,{0,1,2,3},∅,by decide,by decide⟩

end PEqualNP.Research.Transport3321

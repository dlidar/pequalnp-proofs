import Convert
import Three
namespace InverterBridge
open Finset PEqualNP.Research.TripleFormulaMass

def pack3 (v : Fin 3 → Bool) : Fin 8 :=
  ⟨(v 0).toNat + 2*(v 1).toNat + 4*(v 2).toNat, by
    have a := Bool.toNat_le (v 0); have b := Bool.toNat_le (v 1); have c := Bool.toNat_le (v 2); omega⟩

theorem parallel_implies : ∀ x y : Fin 3 → Bool,
    Three.parallel (pack3 x) (pack3 y)=false → (x≤y ∨ y≤x) := by decide +kernel

def mask8 (f : Fin 8 → Bool) : Fin 256 :=
  ⟨(BitVec.ofBoolListLE (List.ofFn f)).toNat, by
    have h := (BitVec.ofBoolListLE (List.ofFn f)).isLt
    simpa using h⟩

theorem mask8_read (f : Fin 8 → Bool) (j : Fin 8) : (mask8 f).val.testBit j.val=f j := by
  simp only [mask8,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos j.isLt,Option.getD_some]

def Value.pick3 {I} (k : Fin 11) (s : Fin 3 → I) : Value I :=
  let a : Formula I := .var (s 0)
  let b : Formula I := .var (s 1)
  let c : Formula I := .var (s 2)
  ![.fixed false,.fixed true,.term a,.term b,.term c,.term (.conj a b),.term (.conj a c),
    .term (.conj b c),.term (.disj a b),.term (.disj a c),.term (.disj b c)] k

theorem pick3_table : ∀ k : Fin 11, ∀ v : Fin 3 → Bool,
    (Value.pick3 k id).eval v=(Three.pool k).testBit (pack3 v).val := by decide +kernel

theorem pick3_eval {I} (k : Fin 11) (s : Fin 3 → I) (x : X I) :
    (Value.pick3 k s).eval x=(Three.pool k).testBit (pack3 (x ∘ s)).val := by
  rw [← pick3_table]; fin_cases k <;> rfl

theorem pick3_leaves {I} (k : Fin 11) (s : Fin 3 → I) : (Value.pick3 k s).leaves≤2 := by
  fin_cases k <;> first | exact Nat.zero_le _ | exact (by decide : 1≤2) | exact le_rfl

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem three_cover (S : Finset I) (hs : S.card≤3) : ∃ s : Fin 3 → I, ∀ i∈S,∃ j,s j=i := by
  classical
  by_cases h : S.Nonempty
  · obtain ⟨a,ha⟩ := h
    obtain ⟨b,d,ok⟩ := pair_cover (S.erase a) (by rw [card_erase_of_mem ha];omega)
    refine ⟨![a,b,d],?_⟩
    intro i hi
    by_cases e : i=a
    · exact ⟨0,e.symm⟩
    · rcases ok i (mem_erase.mpr ⟨e,hi⟩) with r|r
      · exact ⟨1,r.symm⟩
      · exact ⟨2,r.symm⟩
  · exact ⟨fun _ => Classical.arbitrary I,fun i hi => (h ⟨i,hi⟩).elim⟩

theorem replace_three {P Q : Finset I} {A B F G : X I → Bool}
    (am : Monotone A) (bm : Monotone B) (fm : Monotone F) (gm : Antitone G)
    (ad : Depends A P) (bd : Depends B Q) (hg : ∀ x,A x=true → B x=false → F x=G x)
    (s : Fin 3 → I) (sub : ∀ i∈P ∩ Q, ∃ j,s j=i) :
    ∃ k : Fin 11, ∀ x,A x=true → B x=false → F x=(Value.pick3 k s).eval x := by
  classical
  let code (x : X I) := pack3 (x ∘ s)
  have same {x y : X I} (xy : x≤y) (ax : A x=true) (bx : B x=false) (ay : A y=true) (byy : B y=false) :
      F x=F y := le_antisymm (fm xy) (by simpa only [hg x ax bx,hg y ay byy] using gm xy)
  have norm (x : X I) (ax : A x=true) (bx : B x=false) : F x=F (anchor P Q x) := by
    obtain ⟨h1,h2,a1,b1,a2,b2⟩ := anchors am bm ad bd ax bx
    exact (same h1 ax bx a1 b1).trans (same h2 a2 b2 a1 b1).symm
  have ordered {x y : X I} (ax : A x=true) (bx : B x=false) (ay : A y=true) (byy : B y=false)
      (le : x ∘ s ≤ y ∘ s) : F x=F y := by
    have h : anchor P Q x ≤ anchor P Q y := by
      intro t; by_cases hp : t∈P <;> by_cases hq : t∈Q <;> simp [anchor,hp,hq]
      obtain ⟨j,rfl⟩ := sub t (mem_inter.mpr ⟨hp,hq⟩);exact le j
    obtain ⟨_,_,_,_,a1,b1⟩ := anchors am bm ad bd ax bx
    obtain ⟨_,_,_,_,a2,b2⟩ := anchors am bm ad bd ay byy
    exact (norm x ax bx).trans ((same h a1 b1 a2 b2).trans (norm y ay byy).symm)
  let zero (i : Fin 8) := decide (∃ y : X I, A y=true ∧ B y=false ∧ F y=false ∧ code y=i)
  obtain ⟨k,hk⟩ := Three.every_zero_set (mask8 zero)
  refine ⟨k,?_⟩
  intro x ax bx
  rw [pick3_eval]
  cases fx : F x with
  | false =>
    exact ((hk (code x)).1 (by rw [mask8_read];exact decide_eq_true ⟨x,ax,bx,fx,rfl⟩)).symm
  | true =>
    apply Eq.symm; apply (hk (code x)).2;apply decide_eq_true
    intro j hj
    rw [mask8_read] at hj
    obtain ⟨y,ay,byy,fy,rfl⟩ := of_decide_eq_true hj
    cases v : Three.parallel (code x) (code y) with
    | true => rfl
    | false =>
      rcases parallel_implies _ _ v with le|le
      · have e := ordered ax bx ay byy le;simp [fx,fy] at e
      · have e := ordered ay byy ax bx le;simp [fx,fy] at e


theorem Context.three_mixed (c : Context I) (G : X I → Bool) (anti : Antitone G)
    (mono : Monotone (fun x => c.eval x (G x)))
    (essential : ∀ i, ∃ x y : X I,x≤y ∧ (∀ j,j≠i → x j=y j) ∧ c.eval x (G x)=false ∧ c.eval y (G y)=true)
    (small : c.rawLeaves≤Fintype.card I+3) :
    ∃ f : Formula I, f.leaves≤c.rawLeaves+2 ∧ ∀ x,f.eval x=c.eval x (G x) := by
  classical
  have count := c.mixed_count anti essential
  obtain ⟨s,hs⟩ := three_cover (c.posVars ∩ c.negVars) (by omega)
  obtain ⟨k,hk⟩ := replace_three c.req_mono c.ban_mono mono anti c.req_dep c.ban_dep
    (fun x a b => c.pass x (G x) a b) s hs
  let v := Value.pick3 k s
  have ev (x : X I) : (c.plug v).eval x=c.eval x (G x) := by
    rw [c.plug_eval]; by_contra ne
    obtain ⟨a,b⟩ := c.active x ne
    exact ne ((c.pass x _ a b).trans (hk x a b).symm)
  have ct := (c.plug_count v).trans (Nat.add_le_add_left (pick3_leaves k s) _)
  cases eq : c.plug v with
  | fixed b =>
    obtain ⟨x,y,_,_,h0,h1⟩ := essential (s 0)
    have e0 := ev x; have e1 := ev y
    rw [eq,h0] at e0; rw [eq,h1] at e1
    exact False.elim (Bool.noConfusion (e0.symm.trans e1))
  | term f =>
    exact ⟨f,by simpa [eq,Value.leaves] using ct,fun x => by simpa [eq,Value.eval] using ev x⟩
end InverterBridge

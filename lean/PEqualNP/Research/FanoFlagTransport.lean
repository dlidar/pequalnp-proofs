import PEqualNP.Defs

namespace PEqualNP.Research.FanoFlagTransport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover

abbrev V := Fin 14
def pt (p : Fin 7) : V := Fin.castAdd 7 p
def ln (l : Fin 7) : V := Fin.natAdd 7 l
def mult (p l : Fin 7) := if p = l then 1 else if (p.val+7-l.val)%7 = 1 then 2 else 4
def perm (p l : Fin 7) (v : V) : V :=
  if v.val < 7 then pt ⟨(p.val+mult p l*v.val)%7,by omega⟩
  else ln ⟨(l.val+mult p l*(v.val-7))%7,by omega⟩
def near (v w : V) : Prop := v.val < 7 ∧ 7 ≤ w.val ∧ (v.val + 14 - w.val) % 7 ∈ ([0,1,3] : List Nat)
instance (v w : V) : Decidable (near v w) := by unfold near; infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
theorem maps : ∀ p l, p ∈ fanoLines l → perm p l 0 = pt p ∧ perm p l 7 = ln l ∧
    (∀ u v, perm p l u = perm p l v → u = v) ∧
    (∀ u v, near (perm p l u) (perm p l v) ↔ near u v) := by decide

def wm (e : V ≃ V) (k : Nat) := if h : k < 14 then (e ⟨k,h⟩).val else k
theorem wm_inj (e : V ≃ V) : Function.Injective (wm e) := by
  intro a b h
  unfold wm at h
  split at h <;> split at h
  · exact congrArg Fin.val (e.injective (Fin.ext h))
  · have := (e ⟨a,by assumption⟩).isLt; omega
  · have := (e ⟨b,by assumption⟩).isLt; omega
  · exact h

def gate (e : V ≃ V) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wm e)⟩
def rename (e : V ≃ V) (C : Circuit) : Circuit := ⟨C.gates.map (gate e),wm e C.output⟩

theorem legal (e : V ≃ V) (C : Circuit) (h : IsAO2 14 C) (hn : ∀ g ∈ C.gates,g.inputs.Nodup) :
    IsAO2 14 (rename e C) ∧ ∀ g ∈ (rename e C).gates,g.inputs.Nodup := by
  obtain ⟨ops,back,arity⟩ := h
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ops a ha
  · intro j hj i hi
    change j < (C.gates.map (gate e)).length at hj
    simp only [List.length_map] at hj
    simp only [gateAt,rename,List.getD_eq_getElem _ _ (by simpa using hj : j < (C.gates.map (gate e)).length),List.getElem_map,gate] at hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    have hh := back j hj k (by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact hk)
    unfold wm
    split
    · have := (e ⟨k,by assumption⟩).isLt; omega
    · exact hh
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using arity a ha
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact (hn a ha).map (wm_inj e)

def step {α : Type} (op : GateOp → List α → α) (d : α) (w : List α) (g : Gate) :=
  w ++ [op g.op (g.inputs.map (fun k => w.getD k d))]

theorem simulate {α : Type} (op : GateOp → List α → α) (d : α) (e : V ≃ V) (gs : List Gate)
    (w z : List α) (lb : 14 ≤ w.length) (len : z.length = w.length)
    (rel : ∀ k, z.getD (wm e k) d = w.getD k d) (k : Nat) :
    ((gs.map (gate e)).foldl (step op d) z).getD (wm e k) d =
    (gs.foldl (step op d) w).getD k d := by
  induction gs generalizing w z with
  | nil => exact rel k
  | cons g gs ih =>
    apply ih
    · simp [step]; omega
    · simp [step,len]
    · intro i
      have vals : (g.inputs.map (wm e)).map (fun j => z.getD j d) = g.inputs.map (fun j => w.getD j d) := by
        rw [List.map_map]; exact List.map_congr_left (fun j _ => rel j)
      simp only [step,gate,vals]
      by_cases hi : i < w.length
      · have hz : wm e i < z.length := by unfold wm; split <;> first | exact (by omega) | (have hh := (e ⟨i,by assumption⟩).isLt; omega)
        rw [List.getD_append _ _ _ _ hz,List.getD_append _ _ _ _ hi,rel]
      · have hz : wm e i = i := by simp [wm,show ¬i<14 by omega]
        rw [hz]
        rw [List.getD_append_right _ _ _ _ (by omega : z.length ≤ i), List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),len]

theorem init {α : Type} (x : V → α) (e : V ≃ V) (d : α) (k : Nat) :
    (List.ofFn x).getD (wm e k) d = (List.ofFn (x ∘ e)).getD k d := by
  by_cases h : k < 14
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn,wm,dif_pos h]; exact (e ⟨k,h⟩).isLt),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
    simp only [List.getElem_ofFn,wm,dif_pos h,Function.comp_apply]
  · simp only [wm,dif_neg h]
    rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

theorem eval_rename (e : V ≃ V) (C : Circuit) (x : V → Bool) :
    (rename e C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e)) :=
  simulate GateOp.eval false e C.gates _ _ (by simp) (by simp) (init x e false) C.output


attribute [local instance] lineDegreeGateOpDecEq

def foldDegree (op : GateOp) (xs : List Nat) := if op = .and then xs.sum else xs.foldr max 0

theorem deg_rename (e : V ≃ V) (C : Circuit) (v : V) :
    (rename e C).lineDeg 14 {(e v).val} = C.lineDeg 14 {v.val} := by
  let start (v : V) := (List.range 14).map (fun i => if i ∈ ({v.val} : Finset Nat) then 1 else 0)
  have rel (k : Nat) : (start (e v)).getD (wm e k) 0 = (start v).getD k 0 := by
    by_cases hk : k < 14
    · have hw : wm e k < 14 := by simpa only [wm,dif_pos hk] using (e ⟨k,hk⟩).isLt
      rw [List.getD_eq_getElem _ _ (by simpa only [start,List.length_map,List.length_range] using hw),
        List.getD_eq_getElem _ _ (by simpa only [start,List.length_map,List.length_range] using hk)]
      simp only [start,List.getElem_map,List.getElem_range, Finset.mem_singleton,wm,dif_pos hk]
      by_cases h : k = v.val
      · subst k; simp
      · have ne : (e ⟨k,hk⟩).val ≠ (e v).val := fun he => h (congrArg Fin.val (e.injective (Fin.ext he)))
        simp [ne,h]
    · simp only [wm,dif_neg hk]
      rw [List.getD_eq_default _ _ (by simp only [start,List.length_map,List.length_range]; omega),
        List.getD_eq_default _ _ (by simp only [start,List.length_map,List.length_range]; omega)]
  have step_eq (w : List Nat) (g : Gate) :
      step foldDegree 0 w g = w ++ [g.lineDegree w] := by
    simp only [step,foldDegree,Gate.lineDegree]
  have h := simulate foldDegree 0 e C.gates (start v) (start (e v)) (by simp [start]) (by simp [start]) rel C.output
  simpa only [step_eq,rename,Circuit.lineDeg,Circuit.lineDegrees,start,show step foldDegree 0 = _ from funext fun w => funext (step_eq w)] using h

theorem geo : ∀ v w, near v w ↔ ∃ p l, v = pt p ∧ w = ln l ∧ p ∈ fanoLines l := by decide

def pointSet (x : V → Bool) := Finset.univ.filter (fun p => x (pt p) = true)
def lineSet (x : V → Bool) := Finset.univ.filter (fun l => x (ln l) = true)
def bit (X Y : Finset (Fin 7)) : V → Bool := Fin.append (fun i => decide (i∈X)) (fun j => decide (j∈Y))

theorem encode (x : V → Bool) : incidenceInput (pointSet x) (lineSet x) = List.ofFn x := by
  have hp (i) : decide (i ∈ pointSet x) = x (pt i) := by apply Bool.eq_iff_iff.mpr; simp [pointSet]
  have hl (i) : decide (i ∈ lineSet x) = x (ln i) := by apply Bool.eq_iff_iff.mpr; simp [lineSet]
  rw [List.ofFn_add (n := 7) (m := 7)]
  simp only [incidenceInput,hp,hl]
  rfl

def truth (x : V → Bool) := ∃ v w, near v w ∧ x v = true ∧ x w = true

theorem sem (C : Circuit) : ComputesIncidence fanoLines C ↔
    ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔ truth x := by
  have expand (x : V → Bool) : truth x ↔ ∃ p l, p ∈ fanoLines l ∧ x (pt p) = true ∧ x (ln l) = true := by
    constructor
    · rintro ⟨v,w,h,hv,hw⟩
      obtain ⟨p,l,rfl,rfl,hh⟩ := (geo v w).mp h
      exact ⟨p,l,hh,hv,hw⟩
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨_,_,(geo ..).mpr ⟨_,_,rfl,rfl,h⟩,hp,hl⟩
  constructor
  · intro h x
    rw [← encode x,h,expand]
    simp [incidenceFun,pointSet,lineSet]
    constructor
    · rintro ⟨p,hp,l,hl,hi⟩; exact ⟨p,l,hi,hp,hl⟩
    · rintro ⟨p,l,hi,hp,hl⟩; exact ⟨p,hp,l,hl,hi⟩
  · intro h X Y
    have hb := h (bit X Y)
    rw [expand] at hb
    simp only [bit,List.ofFn_fin_append,pt,ln,Fin.append_left,Fin.append_right,decide_eq_true_eq] at hb
    apply Bool.eq_iff_iff.mpr
    simp only [incidenceInput,incidenceFun,decide_eq_true_eq] at *
    rw [hb]
    constructor
    · rintro ⟨p,l,hi,hp,hl⟩; exact ⟨p,hp,l,hl,hi⟩
    · rintro ⟨p,hp,l,hl,hi⟩; exact ⟨p,l,hi,hp,hl⟩

theorem transport :
∀ (C : Circuit) (p l : Fin 7), p ∈ fanoLines l → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    ComputesIncidence fanoLines C → ∃ (D : Circuit) (e : Fin 14 ≃ Fin 14),
    e 0 = Fin.castAdd 7 p ∧ e 7 = Fin.natAdd 7 l ∧ D.size = C.size ∧ IsAO2 14 D ∧
    (∀ g ∈ D.gates, g.inputs.Nodup) ∧ ComputesIncidence fanoLines D ∧
    D.lineDeg 14 {0} = C.lineDeg 14 {p.val} ∧ D.lineDeg 14 {7} = C.lineDeg 14 {7+l.val} ∧
    ∀ x : Fin 14 → Bool, D.eval (List.ofFn (x ∘ e)) = C.eval (List.ofFn x) := by
  intro C p l hflag ha hn hc
  obtain ⟨hp,hl,hinj,hgeo⟩ := maps p l hflag
  let e : V ≃ V := Equiv.ofBijective (perm p l) ((Finite.injective_iff_bijective).mp hinj)
  have key (v w : V) : near (e v) (e w) ↔ near v w := hgeo v w
  have hde := legal e.symm C ha hn
  refine ⟨rename e.symm C,e,hp,hl,by simp [rename,Circuit.size],hde.1,hde.2,?_,?_,?_,?_⟩
  · apply (sem _).mpr
    intro x
    rw [eval_rename,(sem _).mp hc]
    constructor
    · rintro ⟨v,w,h,hv,hw⟩
      exact ⟨e.symm v,e.symm w,(key ..).mp (by simpa using h),hv,hw⟩
    · rintro ⟨v,w,h,hv,hw⟩
      exact ⟨e v,e w,(key ..).mpr h,by simpa using hv,by simpa using hw⟩
  · have h := deg_rename e.symm C (e 0)
    rw [e.symm_apply_apply] at h
    change e 0 = pt p at hp
    rw [hp] at h
    exact h
  · have h := deg_rename e.symm C (e 7)
    rw [e.symm_apply_apply] at h
    change e 7 = ln l at hl
    rw [hl] at h
    exact h
  · intro x
    rw [eval_rename]
    simp [Function.comp_assoc]

end PEqualNP.Research.FanoFlagTransport

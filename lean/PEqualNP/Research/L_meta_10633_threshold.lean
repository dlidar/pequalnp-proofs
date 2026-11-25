import PEqualNP.Research.L_meta_10633_frontiers

namespace PEqualNP.Research.DenseExactRepair
open PEqualNP.Research.DenseRepairs PEqualNP.Research.DenseFormulaCertificate
open PEqualNP.Research.UniversalInverterRepair

def demanded (j : Bool) (s : Mask) : Score := ((if j then #[0, 278506, 48861, 310984, 163319, 425442, 195797, 457920, 89020, 359336, 129692, 391816, 227764, 489888, 260244, 522368, 104307, 374626, 112209, 374336, 259443, 521570, 259153, 521280, 119600, 389920, 127504, 389632, 258352, 520480, 258064, 520192, 134927, 405258, 175629, 437768, 158983, 421122, 191493, 453632, 215820, 486152, 256524, 518664, 223492, 485632, 256004, 518144, 231171, 501506, 239105, 501248, 255235, 517378, 254977, 517120, 246528, 516864, 254464, 516608, 254208, 516352, 253952, 516096, 262399, 270570, 303325, 303304, 418039, 418018, 450773, 450752, 344252, 352424, 385180, 385160, 483508, 483488, 516244, 516224, 360563, 368738, 368721, 368704, 516211, 516194, 516177, 516160, 376880, 385056, 385040, 385024, 516144, 516128, 516112, 516096, 393231, 401418, 434189, 434184, 417799, 417794, 450565, 450560, 475148, 483336, 516108, 516104, 483332, 483328, 516100, 516096, 491523, 499714, 499713, 499712, 516099, 516098, 516097, 516096, 507904, 516096, 516096, 516096, 516096, 516096, 516096, 516096] else #[0, 278506, 48861, 16383, 163319, 16383, 16383, 16383, 89020, 8190, 8189, 8191, 24575, 8191, 8191, 8191, 104307, 8187, 40959, 8191, 8183, 8191, 8191, 8191, 73727, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 134927, 8175, 8159, 8191, 139263, 8191, 8191, 8191, 8127, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8063, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 262399, 270335, 7935, 8191, 7679, 8191, 8191, 8191, 7167, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 6143, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 4095, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191, 8191] : Array Score)[s.toNat]?.getD 0)

private theorem demanded_spec : ∀ j s, s ≠ 0 → ∀ i : Fin 19,
    (demanded j s).getLsbD i.val = (signal j s (panel i) != graph (panel i)) := by decide +kernel

theorem must_cover {j : Bool} {s : Mask} {t : Tree} (hs : s ≠ 0)
    (h : Fits (fun x : Finset (Fin 7) => graph (maskOf x)) (fun x => signal j s (maskOf x))
      (fun x => t.eval (maskOf x))) : dominated (demanded j s) (score t) := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 19 := ⟨k,hk⟩
  change ((demanded j s) &&& score t).getLsbD i.val = (demanded j s).getLsbD i.val
  rw [BitVec.getLsbD_and,demanded_spec j s hs i,score_spec t i]
  obtain ⟨p,n⟩ := h
  specialize p (rawRow (panel i))
  specialize n (rawRow (panel i))
  simp only [mask_roundtrip] at p n
  exact (by decide : ∀ g d r : Bool, (g = true → d = false → r = true) →
    (g = false → d = true → r = false) → ((d != g) && (r == g)) = (d != g)) _ _ _ p n

private theorem uncovered : ∀ j s, s ≠ 0 → repair j s = none →
    budget s ≤ 3 ∧ ∀ k : Fin 4, k.val ≤ budget s → covered k.val (demanded j s) = false := by
  decide +kernel

theorem exact_fit (j : Bool) (s : Mask) (hs : s ≠ 0) :
    (repair j s).isSome = true ↔ ∃ t : Tree, t.size ≤ budget s ∧
    Fits (fun x : Finset (Fin 7) => graph (maskOf x)) (fun x => signal j s (maskOf x))
      (fun x => t.eval (maskOf x)) := by
  cases hr : repair j s with
  | some t => exact ⟨fun _ => ⟨t,repair_size hr,repair_fits hr⟩, fun _ => rfl⟩
  | none =>
    constructor
    · intro no; contradiction
    · rintro ⟨t,sz,fit⟩
      obtain ⟨low,fail⟩ := uncovered j s hs hr
      have hit := small_tree t (sz.trans low)
      obtain ⟨a,ha,dom⟩ := List.any_eq_true.mp hit
      have cover : covered t.size (demanded j s) :=
        List.any_eq_true.mpr ⟨a,ha,transitive _ _ _ (must_cover hs fit) dom⟩
      have eqfalse := fail ⟨t.size,by omega⟩ sz
      simp_all

private theorem back : ∀ x : Finset (Fin 7), rawRow (maskOf x) = x := by decide +kernel

private theorem incl {x y : Finset (Fin 7)} (h : x ⊆ y) : maskOf x &&& maskOf y = maskOf x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have point (hi' : (maskOf x).getLsbD i = true) : (maskOf y).getLsbD i = true := by
    have hx : (⟨i,hi⟩ : Fin 7) ∈ rawRow (maskOf x) := by simp [rawRow,hi']
    rw [back] at hx
    have hy := h hx
    rw [←back y] at hy
    exact (Finset.mem_filter.mp hy).2
  simp only [BitVec.getLsbD_and]
  cases hx : (maskOf x).getLsbD i
  · rfl
  · rw [point hx]; rfl

private theorem mask_order (a b e : Mask) (h : a &&& b = a) :
    ((a &&& e) == e) ≤ ((b &&& e) == e) ∧ ((a &&& e) != 0) ≤ ((b &&& e) != 0) := by
  simp only [Bool.le_iff_imp,beq_iff_eq,bne_iff_ne]
  constructor
  · intro ha
    calc b &&& e = b &&& (a &&& e) := by rw [ha]
         _ = (a &&& b) &&& e := by rw [←BitVec.and_assoc,BitVec.and_comm b a]
         _ = e := by rw [h,ha]
  · intro ha hb
    apply ha
    calc a &&& e = (a &&& b) &&& e := by rw [h]
         _ = a &&& (b &&& e) := BitVec.and_assoc _ _ _
         _ = 0 := by rw [hb]; exact BitVec.and_zero

theorem graph_mono : Monotone (fun x : Finset (Fin 7) => graph (maskOf x)) := by
  intro x y h
  simp only [graph,Bool.le_iff_imp,List.any_eq_true]
  rintro ⟨e,he,ok⟩
  exact ⟨e,he,Bool.le_iff_imp.mp (mask_order _ _ e (incl h)).1 ok⟩

theorem signal_mono (j : Bool) (s : Mask) : Monotone (fun x : Finset (Fin 7) => signal j s (maskOf x)) := by
  intro x y h
  have m := mask_order _ _ s (incl h)
  cases j <;> first | exact m.1 | exact m.2

theorem exact_universal (j : Bool) (s : Mask) (hs : s ≠ 0) :
    (repair j s).isSome = true ↔ ∃ t : Tree, t.size ≤ budget s ∧
    Safe (fun x : Finset (Fin 7) => graph (maskOf x)) (fun x => signal j s (maskOf x))
      (fun x => t.eval (maskOf x)) := by
  simpa only [safe_iff graph_mono (signal_mono j s)] using exact_fit j s hs

end PEqualNP.Research.DenseExactRepair

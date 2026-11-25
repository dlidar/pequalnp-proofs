import PEqualNP.Research.L_meta_10633_repairs

namespace PEqualNP.Research.DenseFormulaCertificate
open PEqualNP.Research.DenseRepairs
open PEqualNP.Research.UniversalInverterRepair

/-- A set bit indicates success on that positive or negative test. -/
abbrev Score := BitVec 19
def positive : Score := 8191
def negative : Score := 516096
def panel (i : Fin 19) : Mask := ([9, 10, 17, 20, 33, 34, 40, 48, 66, 68, 72, 80, 96, 7, 12, 18, 24, 36, 65] : List Mask)[i.val]!
def column (i : Fin 7) : Score := ([245781, 475426, 360968, 435267, 419980, 389360, 261888] : List Score)[i.val]!

def combine (j : Bool) (a b : Score) : Score :=
  if j then ((a ||| b) &&& positive) ||| ((a &&& b) &&& negative)
  else ((a &&& b) &&& positive) ||| ((a ||| b) &&& negative)

def score : Tree → Score
  | .input i => column i
  | .lit b => if b then positive else negative
  | .join a b => combine true (score a) (score b)
  | .meet a b => combine false (score a) (score b)

def dominated (a b : Score) : Bool := (a &&& b) == a

theorem transitive (a b c : Score) (h : dominated a b) (h' : dominated b c) : dominated a c := by
  have H := beq_iff_eq.mp h
  have K := beq_iff_eq.mp h'
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have A := congrArg (fun x : Score => x.getLsbD i) H
  have B := congrArg (fun x : Score => x.getLsbD i) K
  simp only [BitVec.getLsbD_and] at A B ⊢
  exact (by decide : ∀ x y z : Bool, (x && y) = x → (y && z) = y → (x && z) = x) _ _ _ A B

theorem combine_mono (j : Bool) (a b c d : Score) (ha : dominated a c) (hb : dominated b d) :
    dominated (combine j a b) (combine j c d) := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have A := congrArg (fun x : Score => x.getLsbD i) (beq_iff_eq.mp ha)
  have B := congrArg (fun x : Score => x.getLsbD i) (beq_iff_eq.mp hb)
  simp only [BitVec.getLsbD_and] at A B
  let op (j x y p n : Bool) := if j then ((x || y) && p) || ((x && y) && n)
    else ((x && y) && p) || ((x || y) && n)
  have lemma1 : ∀ j a b c d p n : Bool, (a && c) = a → (b && d) = b →
      (op j a b p n && op j c d p n) = op j a b p n := by decide
  have result := lemma1 j _ _ _ _ (positive.getLsbD i) (negative.getLsbD i) A B
  cases j <;> simpa only [op,combine,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,
    BitVec.getLsbD_or] using result

private theorem panel_polarity : ∀ i : Fin 19,
    graph (panel i) = decide (i.val < 13) ∧ positive.getLsbD i.val = decide (i.val < 13) ∧
    negative.getLsbD i.val = !(decide (i.val < 13)) := by decide +kernel

theorem score_spec (t : Tree) (i : Fin 19) :
    (score t).getLsbD i.val = (t.eval (panel i) == graph (panel i)) := by
  obtain ⟨h,hp,hn⟩ := panel_polarity i
  induction t with
  | input k => exact (by decide +kernel : ∀ k : Fin 7, ∀ i : Fin 19,
      (column k).getLsbD i.val = ((panel i).getLsbD k.val == graph (panel i))) k i
  | lit b =>
    cases b
    · change negative.getLsbD i.val = (false == graph (panel i))
      rw [hn,h]; cases decide (i.val < 13) <;> rfl
    · change positive.getLsbD i.val = (true == graph (panel i))
      rw [hp,h]; cases decide (i.val < 13) <;> rfl
  | meet a b ha hb =>
    simp only [score,combine,Tree.eval,Bool.false_eq_true,ite_false,BitVec.getLsbD_or,BitVec.getLsbD_and,
      ha,hb,hp,hn,h]
    cases a.eval (panel i) <;> cases b.eval (panel i) <;> cases decide (i.val < 13) <;> rfl
  | join a b ha hb =>
    simp only [score,combine,Tree.eval,ite_true,BitVec.getLsbD_or,BitVec.getLsbD_and,ha,hb,hp,hn,h]
    cases a.eval (panel i) <;> cases b.eval (panel i) <;> cases decide (i.val < 13) <;> rfl

private def stage0 : List Score := [245781, 475426, 360968, 435267, 419980, 389360, 261888, 8191, 516096]

private def stage1 : List Score := [516097, 516098, 516100, 516104, 516112, 516128, 516160, 516224, 516352, 475426, 213303, 516608, 98845, 328490, 517120, 435267, 164951, 394595, 296523, 518144, 419980, 149661, 412078, 264844, 404687, 520192, 389360, 119029, 348658, 365304, 308467, 293116, 261888, 106248, 253717, 220962, 180035, 163724, 131056, 8191, 516096]

private def stage2 : List Score := [516099, 516101, 516108, 516113, 516116, 245783, 245789, 516130, 516144, 245813, 516161, 516162, 516176, 245845, 516192, 516228, 516232, 516240, 245909, 516256, 516288, 516354, 516384, 475427, 475430, 475434, 475442, 475490, 475554, 516616, 360969, 360970, 360972, 516864, 361224, 475938, 66367, 517121, 517122, 517184, 435271, 435275, 435283, 435299, 435395, 517376, 476450, 435523, 132471, 517632, 361992, 435779, 34399, 264043, 518148, 518152, 518272, 419981, 419982, 419996, 420012, 420044, 518400, 477474, 420236, 412078, 149951, 518656, 363016, 420492, 265134, 519168, 437315, 421004, 404687, 134367, 396783, 265935, 520208, 520224, 520256, 520320, 389361, 389362, 389364, 389368, 520448, 479522, 389616, 348658, 86519, 520704, 389872, 365304, 103165, 332794, 521216, 439363, 390384, 308467, 38135, 267763, 300795, 522240, 424076, 391408, 293116, 22781, 285182, 269052, 277759, 261889, 261890, 261892, 261896, 261904, 253717, 106269, 261920, 73514, 220983, 261952, 180035, 40779, 171863, 139107, 262016, 163724, 155549, 155566, 147407, 131056, 90098, 49139, 122869, 106488, 32764, 8191, 516096]

private def stage3 : List Score := [516102, 483335, 516105, 516106, 499725, 516117, 516120, 516132, 516136, 516147, 483380, 245815, 516163, 516168, 507986, 450644, 245847, 508001, 516208, 245877, 516226, 516236, 450705, 508056, 245917, 450722, 508068, 508072, 516272, 245941, 483522, 516293, 499912, 516304, 245973, 516320, 516353, 516356, 516360, 516368, 516386, 475431, 475438, 475443, 475446, 213311, 475491, 475506, 213367, 475558, 475562, 475570, 213431, 475618, 516609, 516610, 516612, 360971, 360973, 516624, 98847, 516640, 516672, 500482, 484104, 361226, 475946, 328491, 328494, 517123, 517128, 517185, 517186, 435279, 435287, 164959, 435315, 164983, 435399, 435403, 435411, 165079, 435427, 509185, 476451, 517472, 476514, 435555, 394611, 509441, 509442, 452104, 361993, 361994, 435787, 296527, 517888, 362248, 476962, 329514, 436035, 296779, 395107, 518146, 518156, 518276, 518280, 419983, 419997, 420014, 420028, 420045, 420046, 420060, 149725, 420076, 452866, 510212, 510216, 477478, 477482, 420238, 518560, 477602, 420268, 412079, 412094, 412142, 510468, 363020, 518912, 363272, 477986, 330538, 420748, 412590, 486402, 519173, 502792, 437319, 437323, 421005, 421006, 519360, 437443, 421068, 404703, 404719, 519424, 478498, 437571, 421260, 413102, 404943, 396783, 134655, 519680, 364040, 437827, 298571, 421516, 405199, 266223, 520240, 520272, 520288, 520336, 520352, 520384, 389363, 389365, 119031, 389372, 119037, 512272, 479538, 520514, 479586, 487808, 479650, 389618, 348659, 348662, 348666, 512528, 512544, 504384, 520840, 389880, 365305, 365306, 365308, 520960, 480034, 390128, 349170, 365560, 332794, 70655, 521233, 521250, 439379, 439395, 455808, 439491, 390385, 390386, 308471, 308475, 521472, 480546, 439619, 398691, 390640, 349682, 308723, 521728, 439875, 390896, 308979, 366328, 300795, 38655, 268283, 522260, 489504, 456768, 424092, 424108, 424140, 391412, 391416, 293117, 293118, 522496, 481570, 424332, 416174, 391664, 350706, 293372, 285182, 23039, 522752, 424588, 391920, 367352, 293628, 269310, 523264, 441411, 425100, 408783, 392432, 310515, 294140, 277759, 269823, 270079, 261891, 261893, 106250, 261900, 261905, 261908, 253719, 253725, 261922, 220970, 261936, 253749, 220983, 73535, 261953, 261954, 180039, 180043, 261968, 180051, 253781, 171863, 40799, 261984, 221026, 180067, 139127, 262020, 262024, 163725, 163726, 262032, 253845, 163740, 262048, 221090, 163756, 155583, 262080, 180163, 163788, 147407, 139231, 139247, 131057, 131058, 49139, 131060, 122869, 40951, 90103, 131064, 73722, 40955, 32764, 24573, 106493, 24574, 16383, 8191, 516096]

def frontier : Nat → List Score
  | 0 => stage0
  | 1 => stage1
  | 2 => stage2
  | _ => stage3

def covered (k : Nat) (a : Score) := (frontier k).any (dominated a)

private theorem seeds : (∀ k : Fin 7, covered 0 (column k)) ∧ covered 1 positive ∧ covered 1 negative := by
  decide +kernel

def closed (j : Bool) (k l : Nat) := (frontier k).all (fun a => (frontier l).all (fun b =>
  covered (1+k+l) (combine j a b)))

private theorem step_0_0_false : closed false 0 0 := by decide +kernel
private theorem step_0_0_true : closed true 0 0 := by decide +kernel
private theorem step_0_1_false : closed false 0 1 := by decide +kernel
private theorem step_0_1_true : closed true 0 1 := by decide +kernel
private theorem step_1_0_false : closed false 1 0 := by decide +kernel
private theorem step_1_0_true : closed true 1 0 := by decide +kernel
private theorem step_0_2_false : closed false 0 2 := by decide +kernel
private theorem step_0_2_true : closed true 0 2 := by decide +kernel
private theorem step_2_0_false : closed false 2 0 := by decide +kernel
private theorem step_2_0_true : closed true 2 0 := by decide +kernel
private theorem step_1_1_false : closed false 1 1 := by decide +kernel
private theorem step_1_1_true : closed true 1 1 := by decide +kernel

private theorem steps (j : Bool) (k l : Nat) (h : 1+k+l ≤ 3) : closed j k l := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hl : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> try omega
  · cases j
    · exact step_0_0_false
    · exact step_0_0_true
  · cases j
    · exact step_0_1_false
    · exact step_0_1_true
  · cases j
    · exact step_0_2_false
    · exact step_0_2_true
  · cases j
    · exact step_1_0_false
    · exact step_1_0_true
  · cases j
    · exact step_1_1_false
    · exact step_1_1_true
  · cases j
    · exact step_2_0_false
    · exact step_2_0_true

private theorem merge (j : Bool) {k l : Nat} {a b : Score} (h : 1+k+l ≤ 3)
    (ca : covered k a) (cb : covered l b) : covered (1+k+l) (combine j a b) := by
  obtain ⟨A,mA,hA⟩ := List.any_eq_true.mp ca
  obtain ⟨B,mB,hB⟩ := List.any_eq_true.mp cb
  have allPairs := steps j k l h
  unfold closed at allPairs
  have link := List.all_eq_true.mp (List.all_eq_true.mp allPairs A mA) B mB
  obtain ⟨C,mC,hC⟩ := List.any_eq_true.mp link
  exact List.any_eq_true.mpr ⟨C,mC,transitive _ _ _ (combine_mono j _ _ _ _ hA hB) hC⟩

theorem small_tree (t : Tree) (h : t.size ≤ 3) : covered t.size (score t) := by
  induction t with
  | input i => exact seeds.1 i
  | lit b =>
    cases b
    · exact seeds.2.2
    · exact seeds.2.1
  | meet a b ha hb =>
    change 1+a.size+b.size ≤ 3 at h
    exact merge false h (ha (by omega)) (hb (by omega))
  | join a b ha hb =>
    change 1+a.size+b.size ≤ 3 at h
    exact merge true h (ha (by omega)) (hb (by omega))

end PEqualNP.Research.DenseFormulaCertificate

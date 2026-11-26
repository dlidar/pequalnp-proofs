import PEqualNP.Research.ColourTables18173

namespace PEqualNP.Research.ColourProfiles18173

open PEqualNP.Outside.L_meta_18113

theorem posted_row (c : Core) (z : Neighbours) :
    posted (input c z) = (row (label c)).getLsbD z.val := by
  let i : Fin 32768 := ⟨32*c.val+z.val, by have := c.isLt; have := z.isLt; omega⟩
  have raw (j : Fin 15) : (rawInputs.getD j.val 0).getLsbD i.val = input c z j := by
    simp only [rawInputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
    simp only [BitVec.getLsbD_ofNat,i.isLt,decide_true,Bool.true_and]
    exact varNat_testBit j i.val i.isLt
  have bits := bvTarget_bit (fun j : Fin 15 => rawInputs.getD j.val 0) i
  rw [← evalBvTarget_eq,← packed_eq,funext raw] at bits
  rw [posted_eq,← bits,slice]
  rw [BitVec.getLsbD_ofNat, Nat.testBit_shiftRight]
  simp only [z.isLt,decide_true,Bool.true_and]
  rfl

def decode7 (m : Fin 128) (z : Neighbours) : Bool :=
  (row ⟨m.val % 83, Nat.mod_lt _ (by decide)⟩).getLsbD z.val

theorem seven_suffice (c : Core) (z : Neighbours) :
    decode7 ⟨(label c).val, by have := (label c).isLt; omega⟩ z = posted (input c z) := by
  rw [posted_row]
  simp [decode7, Nat.mod_eq_of_lt (label c).isLt]

theorem row_ext {a b : Row} (h : ∀ z : Neighbours, a.getLsbD z.val = b.getLsbD z.val) : a = b :=
  BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i,hi⟩

theorem message_lower {M : Type} [Fintype M] (enc : Core → M) (dec : M → Neighbours → Bool)
    (ok : ∀ c z, dec (enc c) z = posted (input c z)) : 83 ≤ Fintype.card M := by
  have inject : Function.Injective (fun i => enc (representative i)) := by
    intro a b eq
    apply distinct
    apply row_ext
    intro z
    have e := congrArg (fun m => dec m z) eq
    simpa only [ok, posted_row, section_label] using e
  simpa using Fintype.card_le_of_injective _ inject

def decoder (m : Finset (Fin 8)) (z : Neighbours) : Bool :=
  decide (∃ i : Label, code i ⊆ m ∧ (row i).getLsbD z.val = true)

theorem monotone_decoder (z : Neighbours) : Monotone (fun m => decoder m z) := by
  intro m m' h
  by_cases hval : decoder m z = true
  · have ht := of_decide_eq_true hval
    obtain ⟨i,hi,yes⟩ := ht
    have yes' : decoder m' z = true := decide_eq_true ⟨i,hi.trans h,yes⟩
    simp [yes']
  · simp [Bool.eq_false_iff.mpr hval]

theorem decode_row (a : Label) (z : Neighbours) :
    decoder (code a) z = (row a).getLsbD z.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [decoder,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,yes⟩
    have e := congrArg (fun r : Row => r.getLsbD z.val) (code_order i a hi)
    simpa [yes] using e
  · exact fun h => ⟨a,Finset.Subset.rfl,h⟩

theorem eight_suffice (c : Core) (z : Neighbours) :
    decoder (code (label c)) z = posted (input c z) := by rw [decode_row,posted_row]

theorem monotone_lower {k : Nat} (enc : Core → Finset (Fin k))
    (dec : Finset (Fin k) → Neighbours → Bool) (mono : ∀ z, Monotone (fun m => dec m z))
    (ok : ∀ c z, dec (enc c) z = posted (input c z)) :
    45 ≤ k.choose (k/2) := by
  let f (i : Fin 45) := enc (representative (separated i))
  have incomparable {i j : Fin 45} (ne : i ≠ j) : ¬ f i ⊆ f j := by
    intro sub
    obtain ⟨z,yes,no⟩ := separates i j ne
    have h := mono z (show f i ≤ f j from sub)
    simp only [f,ok,posted_row,section_label,yes,no] at h
    contradiction
  have inj : Function.Injective f := by
    intro i j eq; by_contra ne; exact incomparable ne (eq ▸ Finset.Subset.rfl)
  let A := Finset.univ.image f
  have ant : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin k))) := by
    intro a ha b hb ne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact incomparable (fun eq => ne (congrArg f eq))
  simpa [A, Finset.card_image_of_injective _ inj] using ant.sperner

theorem at_least_eight {k : Nat} (enc : Core → Finset (Fin k))
    (dec : Finset (Fin k) → Neighbours → Bool) (mono : ∀ z, Monotone (fun m => dec m z))
    (ok : ∀ c z, dec (enc c) z = posted (input c z)) : 8 ≤ k := by
  have b := monotone_lower enc dec mono ok
  by_contra! h
  interval_cases k <;> norm_num [Nat.choose] at b

theorem all_inputs (x : Fin 15 → Bool) : ∃ c : Core, ∃ z : Neighbours, input c z = x := by
  let m := hcsBitsNat x
  have bound : m < 32768 := hcsBitsNat_lt x
  let c : Core := ⟨m / 32,by omega⟩
  let z : Neighbours := ⟨m % 32,Nat.mod_lt _ (by decide)⟩
  refine ⟨c,z,?_⟩
  funext i
  change (32*(m/32)+m%32).testBit _ = _
  rw [show 32*(m/32) + m%32 = m by omega]
  exact hcsBitsNat_testBit x i

theorem exactly_83 : ∃ (enc : Core → Fin 83) (dec : Fin 83 → Neighbours → Bool),
    ∀ c z, dec (enc c) z = posted (input c z) :=
  ⟨label,fun i z => (row i).getLsbD z.val,fun c z => (posted_row c z).symm⟩

theorem at_least_seven {k : Nat} (enc : Core → Fin (2^k))
    (dec : Fin (2^k) → Neighbours → Bool) (ok : ∀ c z, dec (enc c) z = posted (input c z)) :
    7 ≤ k := by
  have h : 83 ≤ 2^k := by simpa using message_lower enc dec ok
  by_contra! small
  interval_cases k <;> norm_num at h

end PEqualNP.Research.ColourProfiles18173

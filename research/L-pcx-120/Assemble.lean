import Family
import OrbitData
namespace PHPOverlap
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph
def idx (v : Grid) : Nat := 3 * v.1.val + v.2.val
def formMask (S : Finset Grid) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : Grid) : idx v < 12 := by
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  unfold idx
  omega

theorem idx_inj : Function.Injective idx := by
  intro v w h
  have hv := v.2.isLt
  have hw := w.2.isLt
  unfold idx at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem mask_insert (S : Finset Grid) {v : Grid} (h : v ∉ S) :
    formMask (insert v S) = 2 ^ idx v ^^^ formMask S := by
  simp [formMask, Finset.fold_insert h]

theorem mask_lt (S : Finset Grid) : formMask S < 4096 := by
  change formMask S < 2 ^ 12
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert v S h ih =>
    rw [mask_insert S h]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) (idx_lt v)) ih

theorem bit_mask (S : Finset Grid) (v : Grid) :
    (formMask S).testBit (idx v) = decide (v ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert w S h ih =>
    rw [mask_insert S h, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hw : v = w
    · subst w
      simp [h]
    · have hidx : idx w ≠ idx v := fun e => hw (idx_inj e.symm)
      simp [hidx, hw]

theorem mask_nz {S : Finset Grid} (h : S.Nonempty) : formMask S ≠ 0 := by
  obtain ⟨v,hv⟩ := h
  intro hz
  have h' := bit_mask S v
  simp [hz,hv] at h'

theorem sat_of_apart {x y : Grid → Bool} (dis : Apart x y) :
    ∀ D ∈ F, ¬LinClauseSat x D → LinClauseSat y D := by
  intro D ⟨C,hC,eq⟩; subst D
  have cs := dis
  have lit {a : Grid → Bool} {v : Grid} {s : Bool} (hm : (v,s) ∈ C) (hv : a v = s) :
      LinClauseSat a (linOfClause C) :=
    ⟨({v},s),Finset.mem_image.mpr ⟨(v,s),hm,rfl⟩,(singleton_sat _ _ _).2 hv⟩
  intro reject
  rcases hC with ⟨i,eq⟩ | ⟨i,j,h,ne,eq⟩
  · subst C
    have off (h : Fin 3) : x (i,h) = false := by
      cases e : x (i,h)
      · rfl
      · exact (reject (lit (Finset.mem_image.mpr ⟨h, Finset.mem_univ _,rfl⟩) e)).elim
    obtain ⟨h,on⟩ := cs.1 i off
    exact lit (Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩) on
  · subst C
    have pi : x (i,h) = true := by
      cases e : x (i,h)
      · exact (reject (lit (by simp) e)).elim
      · rfl
    have pj : x (j,h) = true := by
      cases e : x (j,h)
      · exact (reject (lit (by simp) e)).elim
      · rfl
    rcases cs.2 i j h ne pi pj with e | e
    · exact lit (by simp) e
    · exact lit (by simp) e


theorem sat_ax (D : LinClause Grid) (hd : D ∈ F) : ∃ a, LinClauseSat a D := by
  obtain ⟨C, hC, rfl⟩ := hd
  rcases hC with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact ⟨fun _ => true, ({(i,0)},true), Finset.mem_image.mpr ⟨((i,0),true),Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,rfl⟩,(singleton_sat _ _ _).2 rfl⟩
  · exact ⟨fun _ => false, ({(i,h)},false), Finset.mem_image.mpr ⟨((i,h),false),by simp,rfl⟩,(singleton_sat _ _ _).2 rfl⟩

theorem form_of_entry {m : Nat} (h : rightEntry m = true) :
    (form m).map (move (rowperm m) (colperm m)).toEmbedding = form (key m) := by
  have ⟨hv,_⟩ := Bool.and_eq_true_iff.mp h
  have each := of_decide_eq_true hv
  ext v
  obtain ⟨w,rfl⟩ := (move (rowperm m) (colperm m)).surjective v
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, form, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (each w) ▸ Iff.rfl

theorem allRich
    (routes : ∀ m : Fin 4096, rightEntry m.val = true)
    (wits : ∀ k ∈ keylist.toList, k ≠ 0 → Rich (form k))
    (f : Finset Grid) (ne : f ≠ ∅) : Rich f := by
  let m := formMask f
  have rt := routes ⟨m,mask_lt f⟩
  have nz : m ≠ 0 := mask_nz (Finset.nonempty_iff_ne_empty.mpr ne)
  have nz' : key m ≠ 0 := (of_decide_eq_true (Bool.and_eq_true_iff.mp rt).2).resolve_left nz
  have mem : key m ∈ keylist.toList := by
    unfold key
    cases hx : keylist[code m / 144]? with
    | none => decide
    | some val =>
      simp only [Option.getD_some]
      exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
  have eq : form m = f := by
    ext v
    simp only [form, Finset.mem_filter, Finset.mem_univ, true_and]
    change (formMask f).testBit (idx v) = true ↔ _
    rw [bit_mask]; simp
  rw [← eq]
  exact rich_move _ _ (form_of_entry rt) (wits _ mem nz')

theorem common_lines (rich : ∀ f : Finset Grid, f ≠ ∅ → Rich f)
    (π : List (LinClause Grid)) (hr : IsLinRefutation (PHP 4 3) π) (short : π.length ≤ 51) :
    ∃ C P r c d, Encoded F C P π ∧ r < π.length ∧ P r = [c,d] ∧ c ≠ d ∧
      (∀ a, FalseAt C a r) ∧ 10 ≤ (Live P c ∩ Live P d).card := by
  obtain ⟨C,P,graph⟩ := build_graph hr.1
  obtain ⟨r,lt,fr,_,c,hc,d,hd,neq,parents,f,ne,side⟩ := first_false graph hr.2 sat_ax
  have rule : ∀ i ≤ r, Rule F C P i := fun i hi => graph.1 i (hi.trans_lt lt)
  obtain ⟨n,k,total,⟨a,pa,da⟩,⟨b,pb,db⟩⟩ := rich f ne
  have lo := packed_leaves (fun i hi => rule i (hi.trans hd.le)) a (by
    intro t; have h := side (a t); have p := pa t
    split at h <;> simp_all [OddAt]) (fun i j ne => sat_of_apart (da i j ne))
  have hi := packed_leaves (fun i hi => rule i (hi.trans hc.le)) b (by
    intro t; have h := side (b t); have p := pb t
    split at h <;> simp_all [OddAt]) (fun i j ne => sat_of_apart (db i j ne))
  have count := overlap_bound rule hc hd hi lo
  exact ⟨C,P,r,c,d,graph,lt,parents,neq,fr,by omega⟩
end PHPOverlap

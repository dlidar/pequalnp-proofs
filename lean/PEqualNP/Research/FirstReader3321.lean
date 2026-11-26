import PEqualNP.Research.GateCuts3321
import PEqualNP.Research.L_meta_1739_vertex_restriction
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Research.FirstReader3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.Research.GateCuts3321

abbrev W (pre : List Gate) {n} (x : Fin n → Bool) := wiresFrom pre (List.ofFn x)
abbrev Bit (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
def Hit (S : Finset ℕ) (g : Gate) : Bool := g.inputs.any (fun j => decide (j ∈ S))

theorem initial_le {n} (S : Finset ℕ) (x y : Fin n → Bool)
    (h : ∀ i : Fin n, i.val ∉ S → x i = true → y i = true) :
    ∀ j ∉ S, (List.ofFn x).getD j false = true → (List.ofFn y).getD j false = true := by
  intro j out val
  by_cases hj : j < n
  · simpa only [getD_ofFn n y false ⟨j,hj⟩] using h ⟨j,hj⟩ out (by simpa only [getD_ofFn n x false ⟨j,hj⟩] using val)
  · rw [List.getD_eq_default _ _ (by simp;omega)] at val;contradiction

theorem monotone_off (S : Finset ℕ) (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (avoid : ∀ g ∈ gs, Hit S g = false) :
    ∀ w w' : List Bool, w.length = w'.length →
    (∀ i ∉ S, w.getD i false = true → w'.getD i false = true) →
    ∀ i ∉ S, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ h;exact h
  | cons g rest ih =>
    intro w w' len h
    have ok : ∀ i ∈ g.inputs, i ∉ S := by simpa [Hit,List.any_eq_false] using avoid g List.mem_cons_self
    have grow : Bit g w = true → Bit g w' = true := by
      rcases ops g List.mem_cons_self with a|a
      · simp only [Bit,a,GateOp.eval,List.all_eq_true,List.mem_map,id]
        intro yes b hb
        obtain ⟨i,mem,rfl⟩ := hb
        exact h i (ok i mem) (yes _ ⟨i,mem,rfl⟩)
      · simp only [Bit,a,GateOp.eval,List.any_eq_true,List.mem_map,id]
        rintro ⟨b,⟨i,mem,rfl⟩,yes⟩
        exact ⟨_,⟨i,mem,rfl⟩,h i (ok i mem) yes⟩
    apply ih (fun t ht => ops t (List.mem_cons_of_mem _ ht)) (fun t ht => avoid t (List.mem_cons_of_mem _ ht))
      (w++[Bit g w]) (w'++[Bit g w']) (by simp [len])
    intro j off
    by_cases eq : j = w.length
    · subst j;rw [getD_snoc_eq,len,getD_snoc_eq];exact grow
    · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)];exact h _ off

theorem equal_off (S : Finset ℕ) (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (avoid : ∀ g ∈ gs, Hit S g = false) (w w' : List Bool) (len : w.length = w'.length)
    (eq : ∀ i ∉ S, w.getD i false = w'.getD i false) :
    ∀ i ∉ S, (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  intro i off;apply Bool.eq_iff_iff.mpr
  exact ⟨monotone_off S gs ops avoid w w' len (fun j hj => (eq j hj) ▸ id) i off,
         monotone_off S gs ops avoid w' w len.symm (fun j hj => (eq j hj).symm ▸ id) i off⟩

theorem split_first {α} (p : α → Bool) (xs : List α) (ex : ∃ x ∈ xs, p x = true) :
    ∃ a x b, xs = a ++ x :: b ∧ p x = true ∧ ∀ y ∈ a, p y = false := by
  induction xs with
  | nil => simp at ex
  | cons x xs ih =>
    by_cases hit : p x = true
    · exact ⟨[],x,xs,rfl,hit,by simp⟩
    · obtain ⟨a,y,b,eq,hy,none⟩ := ih (by simpa [hit] using ex)
      exact ⟨x::a,y,b,by simp [eq],hy,by simpa [hit] using none⟩

theorem pivot_eq {n} (v : Fin n) (pre : List Gate) (x : Fin n → Bool)
    (avoid : ∀ g ∈ pre, v.val ∉ g.inputs) :
    ∀ j, j ≠ v.val → (W pre (Function.update x v false)).getD j false =
      (W pre (Function.update x v true)).getD j false := by
  apply agree_except _ _ _ _ avoid (by simp)
  intro j ne
  by_cases hj : j<n
  · rw [getD_ofFn n _ false ⟨j,hj⟩,getD_ofFn n _ false ⟨j,hj⟩]
    have off : (⟨j,hj⟩ : Fin n) ≠ v := fun eq => ne (congrArg Fin.val eq)
    simp [Function.update_of_ne off]
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem cap {n k} {f : Fn n} (v : Fin n) (C : Circuit) (mono : Monotone2 C)
    (ev : ∀ x, C.eval (List.ofFn x) = f x) (low : Lower (cut f v false) k) (S : Finset ℕ)
    (sound : ∀ x i, i ∈ S → (C.wires (List.ofFn (Function.update x v false))).getD i false = false) :
    k + C.gates.countP (Hit S) ≤ C.size := by
  obtain ⟨D,dm,num,de⟩ := VertexRestriction.eliminate_zero_readers v C mono (fun i => decide (i∈S))
    (fun x i hi => sound x i (of_decide_eq_true hi))
  have bd := low D.size ⟨D,fun g hg => ⟨(dm g hg).1.imp_right Or.inl,(dm g hg).2⟩,le_rfl,
    fun x => (de x).trans (ev _)⟩
  change D.size + C.gates.countP (Hit S) = C.size at num
  omega

theorem tail_avoids (S : Finset ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hit : Hit S g = true) (small : (pre++g::post).countP (Hit S) ≤ 1) :
    ∀ t ∈ post, Hit S t = false := by
  rw [List.countP_append,List.countP_cons,if_pos hit] at small
  have h0 : post.countP (Hit S) = 0 := by omega
  simpa using List.countP_eq_zero.mp h0

end PEqualNP.Research.FirstReader3321

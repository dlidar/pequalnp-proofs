import PEqualNP.Research.L_meta_3865_restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.L_meta_3865_restriction

namespace PEqualNP.Research.FlagPinning

private def MonoGate (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private theorem simplify_mono (op : GateOp) (hop : op = .and ∨ op = .or) (m : ℕ)
    (ins : List Stat) : ∀ g ∈ (simplify op m ins).1, MonoGate g := by
  intro g hg
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simplify, simpAnd, simpOr] at hg <;> (subst hg; simp [MonoGate])

private theorem elim_mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, MonoGate g) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ acc.2, MonoGate g) →
      ∀ g ∈ (elim n gs acc).2, MonoGate g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (fun t ht => hgs t (by simp [ht])) (elimStep n acc g)
    intro t ht
    rcases List.mem_append.mp ht with h1 | h1
    · exact h t h1
    · exact simplify_mono _ (hgs g List.mem_cons_self).1 _ _ t (by simpa using h1)

theorem pin_readers :
∀ (n : ℕ) (S : Finset (Fin n)) (C : Circuit), Monotone2 C →
      let pin := fun (x : Fin n → Bool) i => if i ∈ S then false else x i
      let count := C.gates.countP (fun g => g.inputs.any fun k => decide (∃ i ∈ S, (i : ℕ) = k))
      (∃ x, C.eval (List.ofFn (pin x)) = false) →
      ∃ R : Circuit, Monotone2 R ∧ R.size + count ≤ C.size ∧
        ∀ x, R.eval (List.ofFn x) = C.eval (List.ofFn (pin x))
 := by
  intro n S C mono pin count hf
  let label (i : Fin n) : Stat := if i ∈ S then .inl false else .inr i.val
  let init := List.ofFn label
  let acc := elim n C.gates (init, [])
  let reads := fun (g : Gate) => g.inputs.any fun k => decide (∃ i ∈ S, (i : ℕ) = k)
  let T := Finset.univ.filter fun i : Fin C.gates.length => reads (C.gates.get i)
  have cardT : count = T.card := by
    simpa [count, reads, T] using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) reads
  have hmono (g : Gate) (hg : g ∈ C.gates) : MonoGate g := mono g hg
  have nok (g : Gate) (hg : g ∈ C.gates) : NOk g := by
    obtain ⟨hop, hlen⟩ := hmono g hg
    refine ⟨⟨?_, hlen⟩, ?_⟩
    · rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hop with h | h <;> simp [h]
  have num := elim_count n (init, []) C.gates nok (T.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    obtain ⟨j, hm, z, hz, rfl⟩ : ∃ j ∈ (C.gates.get i).inputs, ∃ z ∈ S, z.val = j := by
      simpa [reads] using hr
    refine ⟨C.gates.get i, by simp [i.isLt], z.val, hm, ?_, false, ?_⟩
    · simp [init]; omega
    · rw [elim_getD _ _ _ _ _ (by simp [init])]
      change init.getD z.val (.inl false) = _
      rw [List.getD_eq_getElem _ _ (by simp [init])]
      simp [init,label,hz])
  have bound : acc.2.length + count ≤ C.size := by
    simpa [acc, cardT, Circuit.size, Finset.card_image_of_injective T Fin.val_injective] using num
  have inv (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn (pin x))) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (nok g hg).1)
    refine ⟨by simp [init], ?_⟩
    intro k
    by_cases hk : k < n
    · simp only [init, List.getD_eq_getElem _ _ (by simpa using hk : k < (List.ofFn label).length),
        List.getD_eq_getElem _ _ (by simpa using hk : k < (List.ofFn (pin x)).length), List.getElem_ofFn]
      by_cases hS : (⟨k,hk⟩ : Fin n) ∈ S
      · simp [label, pin, hS, Stat.Valid, Stat.val]
      · simp [label, pin, hS, Stat.Valid, Stat.val, wiresFrom, hk]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial,rfl⟩
  have val (x : Fin n → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn (pin x)) := ((inv x).2 _).2
  cases h : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2,k⟩, elim_mono _ _ hmono _ (by simp), bound, ?_⟩
    intro x
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [h, Stat.val] using val x
  | inl b =>
    have eqb (x : Fin n → Bool) : b = C.eval (List.ofFn (pin x)) := by simpa only [h,Stat.val] using val x
    obtain ⟨x,hx⟩ := hf
    obtain rfl : b = false := (eqb x).trans hx
    refine ⟨⟨[],n⟩, by simp [Monotone2], ?_, ?_⟩
    · change 0 + count ≤ C.size; omega
    · intro y
      refine Eq.trans ?_ (eqb y)
      change (List.ofFn y).getD n false = false
      simp
/-- For each deleted flag, the twelve remaining point-stars have degrees
3,3,3,4,4,4,4,4,4,4,4,4. The point-star construction therefore uses
33 inner ORs, twelve ANDs and eleven outer ORs. -/
theorem residual_profile :
    let D : Finset (Fin 13) := {0,1,3,9}
    ∀ p l : Fin 13, p-l ∈ D →
      let rows := (Finset.univ : Finset (Fin 13)).erase p
      let deg := fun u : Fin 13 => ((Finset.univ.erase l).filter fun v => u-v ∈ D).card
      (rows.filter fun u => deg u = 3).card = 3 ∧
      (rows.filter fun u => deg u = 4).card = 9 ∧
      ∑ u ∈ rows, deg u = 45 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 8000000 in decide +kernel

end PEqualNP.Research.FlagPinning

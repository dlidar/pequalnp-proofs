import PEqualNP.Outside.L_clb_067

namespace RankedCyclicTables

theorem exact_negation : ¬ (∃ (n w : ℕ) (hn : 0 < n) (q : Fin (2 ^ n)),
  let I := n * 2 ^ (w + 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        table i (fun j => pat.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
        table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      q.val < sols.card → ∃ z ∈ sols,
        (sols.filter (fun y => y.val < z.val)).card = q.val ∧
        ∀ pos : Fin n, (C.wires inputs).getD (outBit pos).val false =
          z.val.testBit (n - 1 - pos.val)) ∧
    ∃ k b : ℕ, 0 < k ∧ k ≤ w + 1 ∧ k + b ≤ n ∧ q.val < 2 ^ (k + b) ∧
      2 ^ PEqualNP.NotBracket.notCount C <
        1 + ((n - b) / k) * (2 ^ k - 1) - q.val / 2 ^ b) := by
  rintro ⟨n, w, hn, q, C, outBit, hfan, hback, hselect, k, b, hk, hw, hkb, hq, hlt⟩
  exact (Nat.not_lt_of_ge (PEqualNP.Outside.L_clb_067 n w hn q C outBit hfan hback hselect k b hk hw hkb hq)) hlt

theorem proposed_parameters {u : ℕ} (h : 1 + ((5 - 1) / 2) * (2 ^ 2 - 1) - 3 / 2 ^ 1 ≤ 2 ^ u) : 3 ≤ u := by
  by_contra! hsmall
  interval_cases u <;> norm_num at h

end RankedCyclicTables

#print axioms RankedCyclicTables.exact_negation
#print axioms RankedCyclicTables.proposed_parameters

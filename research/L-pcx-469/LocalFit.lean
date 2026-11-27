import Transport
namespace SpinHash
open Finset SpinMass
variable {t b k I : ℕ}
def blockWord (c : Label t b) (m : Fin I → Mask b) (G : Model t k) (j : Fin I) := reading G (m j ∘ c)

def priced (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ)
    (M : Model b k) : ℕ := if ∃ q, project c (some e) = some q ∧ mult M q = a then
      cost (fun j => (y j).map ((4:ℕ)^k*·)) (fun j => prediction c M (m j)) else I

noncomputable def price (k : ℕ) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ) :=
  (univ : Finset (Model b k)).inf' univ_nonempty (priced c m e a y)

theorem cost_cap {d : ℕ} (y : Fin d → Option ℕ) (f : Fin d → ℕ) : cost y f ≤ d := by
  unfold cost
  have hh := sum_le_sum (s := (univ : Finset (Fin d))) (f := fun i => if y i ≠ none ∧ y i ≠ some (f i) then 1 else 0) (g := fun _ => 1) (fun i _ => by split <;> decide)
  simpa using hh

theorem price_cap (k : ℕ) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ) (y : Fin I → Option ℕ) :
    price k c m e a y ≤ I := by
  unfold price
  apply (inf'_le (fun M : Model b k => priced c m e a y M) (mem_univ (fun _ => none))).trans
  unfold priced;split
  · exact cost_cap _ _
  · rfl

theorem price_true {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (m : Fin I → Mask b) (y : Fin I → Option ℕ) :
    price k c m e (mult G e) y ≤ cost y (blockWord c m G) := by
  let M := fun l => project c (G l)
  have hh : ∃ q, project c (some e) = some q ∧ mult M q = mult G e := project_preserves hc
  have hp (j : Fin I) : prediction c M (m j) = 4^k * blockWord c m G j := prediction_exact hc _
  have h := inf'_le (s := (univ : Finset (Model b k))) (priced c m e (mult G e) y) (mem_univ M)
  change price k c m e (mult G e) y ≤ _ at h
  simpa only [priced,if_pos hh,hp,cost_scaled _ _ _ (by positivity : 0 < (4:ℕ)^k)] using h

theorem price_false {G : Model t k} {e : Pair t} {c : Label t b}
    (hc : ∀ p ∈ critical e G, safe c p) (s : ℕ) (a : ℕ) (ha : a ≠ mult G e)
    (m : Fin I → Mask b) (y : Fin I → Option ℕ)
    (hsep : ∀ (M N : Model b k) (q : Pair b), mult M q ≠ mult N q →
      (8*s-9)*I ≤ 18*s*rowDist m M N) :
    (8*s-9)*I ≤ 18*s*(price k c m e a y + cost y (blockWord c m G) + erasures y) := by
  obtain ⟨M,_,hM⟩ := exists_mem_eq_inf' (s := (univ : Finset (Model b k))) univ_nonempty (priced c m e a y)
  change price k c m e a y = _ at hM
  rw [hM];unfold priced
  split
  · rename_i h
    obtain ⟨q,hq,hm⟩ := h
    let N := fun l => project c (G l)
    obtain ⟨q',hq',hn⟩ := project_preserves hc
    have heq : q' = q := Option.some.inj (hq'.symm.trans hq)
    subst q'
    have hd := hsep M N q (by change mult M q ≠ mult (fun l => project c (G l)) q; omega)
    have hcompare : rowDist m M N = SpinMass.dist (fun j => prediction c M (m j)) (fun j => prediction c N (m j)) := by
      unfold rowDist SpinMass.dist
      simp only [ne_eq,prediction_eq_iff]
    rw [hcompare] at hd
    let yy := fun j => (y j).map ((4:ℕ)^k*·)
    have htri := cost_triangle yy (fun j => prediction c M (m j)) (fun j => prediction c N (m j))
    have hpred (j) : prediction c N (m j) = 4^k * blockWord c m G j := prediction_exact hc _
    have hcst : cost yy (fun j => prediction c N (m j)) = cost y (blockWord c m G) := by
      simp_rw [hpred];exact cost_scaled _ _ _ (by positivity)
    rw [hcst,show erasures yy = erasures y from erasures_scaled _ _] at htri
    exact hd.trans (Nat.mul_le_mul_left _ htri)
  · exact Nat.mul_le_mul (by omega) (by omega)

end SpinHash

import Payload
import Design
namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k I d W U : ℕ}


theorem test_scaled (hU : 4≤U) (hW : W≤U) (i : Fin d) (k T : ℕ) :
    gateP (packet d W) U 5 (fun y => 4^k*((y i).getD 0 % 2^W)=T) := by
  classical
  by_cases h : ∃ a : ℕ, a<2^W ∧ 4^k*a=T
  · obtain ⟨a,ha,rfl⟩ := h
    exact gate_congr _ (matches_constant hU hW i a ha)
      (fun _ => (Nat.mul_right_inj (by positivity : (4:ℕ)^k ≠ 0)).symm)
  · apply gate_congr _ (gate_const (packet d W) U 5 False)
    intro y
    simp only [false_iff]
    intro hh
    exact h ⟨_,Nat.mod_lt _ (by positivity),hh⟩

theorem cost_bit (hU : 4≤U) (hW : W≤U) (i : Fin d) (k T : ℕ) :
    gateP (packet d W) U 10 (fun y =>
      ((clip W (y i)).map ((4:ℕ)^k*·)) ≠ none ∧ ((clip W (y i)).map ((4:ℕ)^k*·)) ≠ some T) := by
  apply gate_congr _ (gate_and _ hU (present_gate (d:=d) (W:=W) (U:=U) (r:=6) i)
    (gate_not _ hU (test_scaled hU hW i k T)))
  intro y;cases hi : y i <;> simp [clip]

theorem cost_cut (hU : 4≤U) (hW : W≤U) (hI : I≤U) (cards : Fin I → Fin d)
    (k : ℕ) (P : Fin I → ℕ) (j : ℕ) :
    gateP (packet d W) U 14 (fun y => j ≤ cost (fun i => (clip W (y (cards i))).map ((4:ℕ)^k*·)) P) := by
  classical
  apply gate_congr _ (gate_card _ hU (by simpa using hI)
    (fun i y => ((clip W (y (cards i))).map ((4:ℕ)^k*·)) ≠ none ∧
      ((clip W (y (cards i))).map ((4:ℕ)^k*·)) ≠ some (P i))
    (fun i => cost_bit hU hW (cards i) k (P i)) j)
  intro y
  unfold cost
  rw [Finset.sum_boole]
  rfl

theorem price_cut (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hM : Fintype.card (Model b k) ≤ U)
    (cards : Fin I → Fin d) (c : Label t b) (m : Fin I → Mask b) (e : Pair t) (a j : ℕ) :
    gateP (packet d W) U 18 (fun y => j ≤ price k c m e a (fun i => clip W (y (cards i)))) := by
  classical
  let P := fun (M : Model b k) (y : Packet d) => j ≤ priced c m e a (fun i => clip W (y (cards i))) M
  have hp (M : Model b k) : gateP (packet d W) U 14 (P M) := by
    by_cases hh : ∃ q, project c (some e) = some q ∧ mult M q = a
    · apply gate_congr _ (cost_cut hU hW hI cards k (fun i => prediction c M (m i)) j)
      intro y;simp only [P,priced,if_pos hh]
    · apply gate_congr _ (gate_const (packet d W) U 14 (j≤I))
      intro y;simp only [P,priced,if_neg hh]
  apply gate_congr _ (gate_all _ hU hM P hp)
  intro y;simp [price,P,le_inf'_iff]

theorem card_lt (n z : ℕ) (h : z ≤ n) : (univ.filter (fun i : Fin n => i.val < z)).card = z := by
  by_cases hz : z<n
  · have hh : (univ.filter (fun i : Fin n => i.val < z)) = Finset.Iio (⟨z,hz⟩ : Fin n) := by ext i;simp; rfl
    rw [hh, Fin.card_Iio]
  · have he := Nat.le_antisymm h (by omega)
    subst z;simp

def rows {H I : ℕ} (W : ℕ) (y : Packet (H*I)) (h : Fin H) (i : Fin I) := clip W (y (finProdFinEquiv (h,i)))

theorem total_as_card {H : ℕ} (f : Fin H → Label t b) (m : Fin I → Mask b)
    (e : Pair t) (a : ℕ) (y : Fin H → Fin I → Option ℕ) :
    totalPrice k f m e a y = (univ.filter (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1))).card := by
  classical
  have h := Finset.sum_boole (R:=ℕ) (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1)) univ
  rw [Nat.cast_id, Fintype.sum_prod_type] at h
  rw [← h];unfold totalPrice
  apply sum_congr rfl;intro i _
  have hh := sum_boole (R:=ℕ) (fun u : Fin I => u.val < price k (f i) m e a (y i)) univ
  rw [Nat.cast_id,card_lt I _ (price_cap ..)] at hh
  exact hh.symm

theorem total_cut {H : ℕ} (hU : 4≤U) (hW : W≤U) (hI : I≤U) (hd : H*I≤U)
    (hM : Fintype.card (Model b k) ≤ U) (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a j : ℕ) :
    gateP (packet (H*I) W) U 22 (fun y => j ≤ totalPrice k f m e a (rows W y)) := by
  classical
  let P := fun (z : Fin H × Fin I) (y : Packet (H*I)) => z.2.val+1 ≤ price k (f z.1) m e a (rows W y z.1)
  have hp (z) : gateP (packet (H*I) W) U 18 (P z) := price_cut hU hW hI hM _ _ _ _ _ _
  apply gate_congr _ (gate_card _ hU (by simpa using hd) P hp j)
  intro y;rw [total_as_card]

theorem price_total_cap {H : ℕ} (f : Fin H → Label t b) (m : Fin I → Mask b) (e : Pair t) (a : ℕ)
    (y : Fin H → Fin I → Option ℕ) : totalPrice k f m e a y ≤ H*I := by
  rw [total_as_card]
  simpa using card_filter_le univ (fun z : Fin H × Fin I => z.2.val+1 ≤ price k (f z.1) m e a (y z.1))

end SpinCircuit

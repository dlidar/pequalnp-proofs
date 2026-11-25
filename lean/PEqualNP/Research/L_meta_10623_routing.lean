import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace PEqualNP.Research.ChannelRouting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w
def trans (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩

theorem simulate (gs : List Gate) (ρ : ℕ → ℕ) (n d : ℕ)
    (lo : ∀ i < n, ρ i < n+d) (hi : ∀ i, n ≤ i → ρ i = i+d)
    (u v : List Bool) (hn : n ≤ u.length) (len : v.length = u.length + d)
    (rel : ∀ i, u.getD i false = v.getD (ρ i) false) :
    ∀ i, (run gs u).getD i false = (run (gs.map (trans ρ)) v).getD (ρ i) false := by
  induction gs generalizing u v with
  | nil => exact rel
  | cons g gs ih =>
    let y := g.op.eval (g.inputs.map (fun i => u.getD i false))
    have same : y = g.op.eval ((g.inputs.map ρ).map (fun i => v.getD i false)) := by
      simp only [List.map_map,Function.comp_def]
      exact congrArg g.op.eval (List.map_congr_left (fun i _ => rel i))
    change ∀ i, (run gs (u++[y])).getD i false = (run (gs.map (trans ρ)) (v++[_])).getD (ρ i) false
    change y = (trans ρ g).op.eval ((trans ρ g).inputs.map (fun i => v.getD i false)) at same
    rw [←same]
    apply ih _ _ (by simp; omega) (by simp; omega)
    intro i
    by_cases h : i < u.length
    · have rho : ρ i < v.length := by
        by_cases a : i < n
        · have := lo i a; omega
        · rw [hi i (by omega)]; omega
      rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ rho,rel]
    · rw [hi i (by omega),List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega

def extend (pre : List Gate) (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨pre ++ C.gates.map (trans ρ), ρ C.output⟩

theorem extend_size (pre : List Gate) (ρ : ℕ → ℕ) (C : Circuit) :
    (extend pre ρ C).size = pre.length + C.size := by simp [extend,Circuit.size]

theorem extend_mono (pre : List Gate) (ρ : ℕ → ℕ) (C : Circuit)
    (hp : Monotone2 ⟨pre,0⟩) (hc : Monotone2 C) : Monotone2 (extend pre ρ C) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hp g h
  · rcases List.mem_map.mp h with ⟨a,ha,rfl⟩
    simpa [trans] using hc a ha

theorem extend_eval (pre : List Gate) (ρ : ℕ → ℕ) (C : Circuit) (w u : List Bool)
    (lo : ∀ i < 5, ρ i < 5+pre.length) (hi : ∀ i, 5 ≤ i → ρ i = i+pre.length)
    (size : u.length = 5) (len : (run pre w).length = 5+pre.length)
    (input : ∀ i, u.getD i false = (run pre w).getD (ρ i) false) :
    (extend pre ρ C).eval w = C.eval u := by
  have e := simulate C.gates ρ 5 pre.length lo hi u (run pre w) (by omega) (by omega) input C.output
  simpa [extend,Circuit.eval,run,Circuit.wires,List.foldl_append] using e.symm

end PEqualNP.Research.ChannelRouting

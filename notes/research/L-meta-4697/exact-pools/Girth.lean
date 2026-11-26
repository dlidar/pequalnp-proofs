import Application
import Example
namespace PEqualNP.Research.Example4697
open Finset PEqualNP.Research.Pool4697
set_option maxHeartbeats 6000000
def labelTable : Array Nat := #[0,3278108365595855434822,0,0,0,0,0,0,0,0,0,0,3277115315460452230958,0,0,0,0,0,0,0,0,0,0,96327860048368580398,769654600205021067632,0,2686494935061143331381,0,0,0,0,0,2605088180455455967605,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1435036992637135375233,0,2034553531867192955308,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2602167353596076215212,0,0,0,0,0,0,2096199516068261026826,0,1951381766353931767139,0,0,0,0,0,0,0,0,0,0,1442940097027491388771,0,0,0,0,0,0,0,0,0,0,0,2106737226790233890899,0,1276760236238628481827,0,0,0,0,0,2097800223953505151770,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2772135385418303996571,0,2770782084680846104796,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,602336871951071926554,0,0,0,0,0,0,1276960615540182226147,0,2688136487717924685523,0,0,0,0,0,0,0,0,0,0,2096158350410937714332,0,0,0,0,0,0,0,0,0,0,0,1949902022320643417828,0,2014666318166743205514,0,0,0,0,0,2096523052785174197475,0,0,0,0,0,0,0,0,0,0,1442657052421887505473,0,0,0,0,0,2623372473278082135852,0,1930482495699641547052,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2117260520562260297354,0,2117235196510681802531,0,0,0,0,0,0,0,0,0,0,1255883798990646229219,0,0,0,0,0,0,0,0,0,0,0,1930507542674289838291,0,2033261635789864637658,0,0,0,0,0,1442611414599725598435,0,0,0,0,0,0,0,0,0,0,1951239512341749465756,0,0,0,0,0,2014625183398812866844,0,1432442878460622428369,0,0,0,0,0,0,0,0,0,0,0,770663412939120297608,0,0,0,0,0,0,0,0,0,0,2615461950728518309093,0,2602496036320328959717,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1445266929480547542737,0,2109331293088747467996,0,0,0,0,0,1927872947394853062300,0,0,0,0,0,0,0,0,0,0,2615302433480586377427,0,0,0,0,0,2012200634609531238618,0,1443948927043675202203,0,0,0,0,0,0,0,0,0,0,0,2623249346649039638611,0,0,0,0,0,0,0,0,0,0,2686804120891778779931,0,770622426768477113114,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3287496566375688544924,0,3278063967159594891492,0,0,0,0,0,96354146408918235345,0,0,0,0,0,0,0,0,0,0,2605131289950629766939,0,0,0,0,0,770831654497337586906,0,2612679318697050191516,0,0,0,0,0,0,0,0,0,0,0,1951584349329054279452,0,0,0,0,0,0,0,0,0,0,1435063381523978139427,0,2602264427279729177683,0,0,0,0,0,0,2109658132669684359690,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2035774082758838925668,0,1928649766988533582179,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2119872285482490410778,0,0,0,0,0,2709389024456291759187,0,1262096520780102580507,0,0,0,0,0,0,0,0,0,0,0,2791858970980650989779,0,0,0,0,0,0,0,0,0,0,2785646495481799263899,0,652038597981388711706,0,0,0,0,0,0,3445405832599283438820,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3395704141203582929116,0,494085778373344413393,3951576969140772157064,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3952685589886336382181,0,0,0,0,0,3553801040815333091109,0]
def label (a b v : V) : Nat := (labelTable[a.val*24+b.val]! >>> (3*v.val)) % 8
def Row (a : V) := ∀ b : V,G.Adj a b → label a b b + 6 ≤ label a b a ∧
    ∀ i j : V,G.Adj i j → s(i,j) ≠ s(a,b) → label a b j ≤ label a b i + 1
private theorem row0 : Row 0 := by unfold Row;decide +kernel
private theorem row1 : Row 1 := by unfold Row;decide +kernel
private theorem row2 : Row 2 := by unfold Row;decide +kernel
private theorem row3 : Row 3 := by unfold Row;decide +kernel
private theorem row4 : Row 4 := by unfold Row;decide +kernel
private theorem row5 : Row 5 := by unfold Row;decide +kernel
private theorem row6 : Row 6 := by unfold Row;decide +kernel
private theorem row7 : Row 7 := by unfold Row;decide +kernel
private theorem row8 : Row 8 := by unfold Row;decide +kernel
private theorem row9 : Row 9 := by unfold Row;decide +kernel
private theorem row10 : Row 10 := by unfold Row;decide +kernel
private theorem row11 : Row 11 := by unfold Row;decide +kernel
private theorem row12 : Row 12 := by unfold Row;decide +kernel
private theorem row13 : Row 13 := by unfold Row;decide +kernel
private theorem row14 : Row 14 := by unfold Row;decide +kernel
private theorem row15 : Row 15 := by unfold Row;decide +kernel
private theorem row16 : Row 16 := by unfold Row;decide +kernel
private theorem row17 : Row 17 := by unfold Row;decide +kernel
private theorem row18 : Row 18 := by unfold Row;decide +kernel
private theorem row19 : Row 19 := by unfold Row;decide +kernel
private theorem row20 : Row 20 := by unfold Row;decide +kernel
private theorem row21 : Row 21 := by unfold Row;decide +kernel
private theorem row22 : Row 22 := by unfold Row;decide +kernel
private theorem row23 : Row 23 := by unfold Row;decide +kernel
theorem labels (a : V) : Row a := by
  fin_cases a <;> first | exact row0 | exact row1 | exact row2 | exact row3 | exact row4 | exact row5 | exact row6 | exact row7 | exact row8 | exact row9 | exact row10 | exact row11 | exact row12 | exact row13 | exact row14 | exact row15 | exact row16 | exact row17 | exact row18 | exact row19 | exact row20 | exact row21 | exact row22 | exact row23
theorem walk_bound {e : Sym2 V} {d : V → Nat}
    (lip : ∀ i j,G.Adj i j → s(i,j) ≠ e → d j ≤ d i+1)
    {x y : V} (p : G.Walk x y) (avoid : e ∉ p.edges) : d y ≤ d x+p.length := by
  induction p with
  | nil => simp
  | @cons a b c edge tail ih =>
    have h₁ : s(a,b) ≠ e := by intro eq;exact avoid (by simp [←eq])
    have h₂ : e ∉ tail.edges := by intro he;exact avoid (by simp [he])
    have first := lip a b edge h₁
    have rest := ih h₂
    simp only [SimpleGraph.Walk.length_cons]
    omega
theorem girth_lower (a : V) (p : G.Walk a a) (h : p.IsCycle) : 7 ≤ p.length := by
  cases p with
  | nil => exact (h.ne_nil rfl).elim
  | @cons _ b _ edge tail =>
    obtain ⟨start,lip⟩ := labels a b edge
    have dist := walk_bound lip tail ((SimpleGraph.Walk.cons_isCycle_iff tail edge).mp h).2
    simp only [SimpleGraph.Walk.length_cons]
    omega
theorem required_49 (h : Posted) (b : Nat)
    (size : PEqualNP.MetaComplexity.HasCircuitSize 24 (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) b) :
    49 ≤ b := by
  have deg : ∀ x ∉ (∅ : Finset V), (G.neighborSet x).ncard=3 := by
    intro x _
    simpa using cubic x
  have edge : ∃ i j : V,G.Adj i j := ⟨0,1,by decide +kernel⟩
  obtain ⟨K,c,k⟩ := posted_iff.mp h 24 G ∅ deg girth_lower (by simp) edge b size
  have t := cover_bound K c
  rw [edge_count] at k
  omega
end PEqualNP.Research.Example4697

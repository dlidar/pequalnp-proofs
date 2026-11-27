import FormulaMass
namespace PEqualNP.Research.Cached18330
open TripleFormulaMass Finset
abbrev Row := Fin 21
abbrev Col := Fin 37
abbrev EdgeInput := Fin 14
abbrev Key := Fin 182
abbrev Weights := Row → Col → Int
def left (r : Row) : EdgeInput := (#[0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6] : Array EdgeInput)[r.val]!
def right (r : Row) : EdgeInput := (#[7, 11, 13, 7, 8, 12, 8, 9, 13, 7, 9, 10, 8, 10, 11, 9, 11, 12, 10, 12, 13] : Array EdgeInput)[r.val]!
def target (x : EdgeInput → Bool) := (List.finRange 21).any fun r => x (left r) && x (right r)
def pos (r : Row) (i : EdgeInput) := ((#[129, 2049, 8193, 130, 258, 4098, 260, 516, 8196, 136, 520, 1032, 272, 1040, 2064, 544, 2080, 4128, 1088, 4160, 8256]: Array Nat)[r.val]!).testBit i.val
def neg (c : Col) (i : EdgeInput) := ((#[127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256]: Array Nat)[c.val]!).testBit i.val
theorem rows_ok : ∀ r,target (pos r)=true := by decide +kernel
theorem cols_ok : ∀ c,target (neg c)=false := by decide +kernel
def pairTab : Array (EdgeInput × EdgeInput) := #[(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (0,12), (0,13), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (1,12), (1,13), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (2,12), (2,13), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (3,12), (3,13), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (4,12), (4,13), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (5,12), (5,13), (6,7), (6,8), (6,9), (6,10), (6,11), (6,12), (6,13), (7,8), (7,9), (7,10), (7,11), (7,12), (7,13), (8,9), (8,10), (8,11), (8,12), (8,13), (9,10), (9,11), (9,12), (9,13), (10,11), (10,12), (10,13), (11,12), (11,13), (12,13)]
def fill (andGate : Bool) (a b : EdgeInput) (x : EdgeInput → Bool) : Option EdgeInput → Bool
  | some i => x i
  | none => if andGate then x a && x b else x a || x b
def extendsKey (k : Key) (x : EdgeInput → Bool) :=
  let pair := pairTab[k.val % 91]!
  fill (decide (k.val < 91)) pair.1 pair.2 x
def keyMatches (k : Key) (andGate : Bool) (a b : EdgeInput) :=
  decide (k.val<91)=andGate ∧ pairTab[k.val % 91]! = (a,b)
theorem every_pair : ∀ (g : Bool) (a b : EdgeInput),a<b → ∃ k,keyMatches k g a b := by
  change ∀ (g : Bool) (a b : Fin 14),a<b → ∃ k : Fin 182,
    decide (k.val<91)=g ∧ pairTab[k.val % 91]! = (a,b)
  decide +kernel
theorem key_extension {k g a b} (h : keyMatches k g a b) (x) : extendsKey k x=fill g a b x := by
  simp [extendsKey,h.1,h.2]
def fails (wt : Weights) (cap : Int) (p : Row → Bool) (q : Col → Bool) : Bool :=
  decide (0 < ((univ.filter (fun r => p r=true)).powerset.filter (fun s =>
    cap < ∑ c∈univ.filter (fun c => q c=false),max 0 (∑ r∈s,wt r c))).card)
theorem score_ok (wt : Weights) (cap : Int) (p : Row → Bool) (q : Col → Bool)
    (h : fails wt cap p q=false) (s : Finset Row) (hm : s∈(univ.filter (fun r => p r=true)).powerset) :
    (∑ c∈univ.filter (fun c => q c=false),max 0 (∑ r∈s,wt r c)) ≤ cap := by
  by_contra! bad
  simp only [fails,decide_eq_false_iff_not,not_lt,Nat.le_zero] at h
  have emp := Finset.card_eq_zero.mp h
  have inc : s ∈ (univ.filter (fun r => p r=true)).powerset.filter (fun t => cap < ∑ c∈univ.filter (fun c => q c=false),max 0 (∑ r∈t,wt r c)) := mem_filter.mpr ⟨hm,bad⟩
  rw [emp] at inc
  exact notMem_empty _ inc
def rawOK (wt : Weights) (cap : Int) : Bool := (List.finRange 14).all fun i =>
  !(fails wt cap (fun r => pos r i) (fun c => neg c i))
def extraOK (wt : Weights) (cap : Int) (k : Key) : Bool :=
  !(fails wt cap (fun r => extendsKey k (pos r) none) (fun c => extendsKey k (neg c) none))
def Bound (b : ℕ) (k : Key) := ∀ f : Formula (Option EdgeInput),
  (∀ x,f.eval (extendsKey k x)=target x) → b ≤ f.leaves
theorem by_cert (b : ℕ) (wt : Weights) (cap : Int) (hcap : 0<cap)
    (total : (b:Int)*cap < mass wt univ univ) (raw : rawOK wt cap=true)
    (k : Key) (extra : extraOK wt cap k=true) : Bound (b+1) k := by
  intro f correct
  have test := atom_from_columns (fun r => extendsKey k (pos r)) (fun c => extendsKey k (neg c)) wt cap (by
    intro i s hm
    cases i with
    | none => exact score_ok _ _ _ _ (by simpa [extraOK] using extra) _ hm
    | some i =>
      have hi := List.all_eq_true.mp raw i (by simp)
      exact score_ok _ _ _ _ (by simpa [extendsKey,fill] using hi) _ hm)
  have h := weight_bound _ _ wt cap test f univ univ (fun r _ => (correct _).trans (rows_ok r))
    (fun c _ => (correct _).trans (cols_ok c))
  by_contra! small
  have le : (f.leaves : Int) ≤ b := by omega
  linarith [mul_le_mul_of_nonneg_left le (le_of_lt hcap)]
end PEqualNP.Research.Cached18330

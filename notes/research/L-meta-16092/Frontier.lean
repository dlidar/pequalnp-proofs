import Samples
namespace PEqualNP.Research.Signed16092
abbrev State := Nat × List W
def nextLists (extra : Nat) (a b : W) (r : List W) : List State :=
  (ops a b).flatMap (fun w =>
    let v := sep w ||| cuts r
    (if v == -1 then [(extra,w::r)] else []) ++
    (if extra != 0 && (v ||| sep a == -1) then [(extra-1,w::a::r)] else []) ++
    (if extra != 0 && (v ||| sep b == -1) then [(extra-1,w::b::r)] else []) ++
    (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra-2,w::a::b::r)] else []))
def children (extra : Nat) (ws : List W) := (pairs ws).flatMap fun (a,b,r) => nextLists extra a b r
theorem any_guard (b : Bool) (s : State) (p : State → Bool) :
    (if b then [s] else []).any p = (b && p s) := by cases b <;> simp
theorem dispatch_as_any (extra : Nat) (next : Nat → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r = (nextLists extra a b r).any (fun s => next s.1 s.2) := by
  simp only [dispatch,nextLists,List.any_flatMap]
  congr 1
  funext w
  simp only [List.any_append,any_guard,Bool.and_or_distrib_left,Bool.and_assoc,Bool.or_assoc]
theorem reject_step (k extra : Nat) (ws : List W)
    (done : (ws == [goal] || ws == [~~~goal])=false)
    (child : ∀ c∈children extra ws,optimized k c.1 c.2=false) :
    optimized (k+1) extra ws=false := by
  simp only [optimized,done,Bool.false_or,dispatch_as_any]
  rw [List.any_eq_false]
  rintro ⟨a,b,r⟩ hp
  intro yes
  obtain ⟨c,hc,eq⟩ := List.any_eq_true.mp yes
  have := child c (List.mem_flatMap.mpr ⟨(a,b,r),hp,hc⟩)
  simp_all
theorem whole_reject (h : optimized 8 3 rows=false) : search 8 rows=false := by
  have only : rows.sublists.filter (fun ws => cuts ws == -1) = [rows] := by decide +kernel
  rw [search,List.any_eq_false]
  intro ws hm
  by_cases hx : cuts ws = -1
  · have heq : ws∈[rows] := only ▸ (List.mem_filter.mpr ⟨hm,by simp [hx]⟩)
    obtain rfl := List.mem_singleton.mp heq
    change ¬(_ && _ && optimized 8 3 rows)=true
    simp [h]
  · have no : (cuts ws == -1)=false := beq_eq_false_iff_ne.mpr hx
    simp only [no,Bool.and_false,Bool.false_and]
    decide
end PEqualNP.Research.Signed16092

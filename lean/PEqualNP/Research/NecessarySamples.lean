import PEqualNP.Research.StarFormulas
import PEqualNP.Research.StarDesign

namespace PEqualNP.Research.NecessarySamples
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.FormulaTrace PEqualNP.Research.StarFormulas
open PEqualNP.Research.StarDesign PEqualNP.Research.NovelTrace

def bits (x : Word) (i : Input) := x.getLsbD i.val

theorem bits_point (x : Word) (p : V) : bits x (point p)=true ↔ p∈pts x := by simp [bits,point,pts]
theorem bits_line (x : Word) (l : V) : bits x (line l)=true ↔ l∈lines x := by simp [bits,line,lines,Nat.add_comm]

theorem edge_primal (x : Word) : edge false (bits x) ↔ ∃ p∈pts x, ∃ l∈lines x,inc p l := by
  simp only [edge,first,second,adj,ite_false,Bool.false_eq_true,decide_eq_true_eq,bits_point,bits_line]
  aesop
theorem edge_dual (x : Word) : edge true (bits x) ↔ edge false (bits x) := by
  simp only [edge,first,second,adj,ite_false,ite_true,Bool.false_eq_true,decide_eq_true_eq]
  aesop

theorem cross_primal (x : Word) (a b) : cross false (bits x) a b ↔ rowHit x a b := by
  simp only [cross,rowHit,first,second,adj,Bool.false_eq_true,ite_false,bits_point,bits_line,decide_eq_true_eq]
theorem cross_dual (x : Word) (a b) : cross true (bits x) a b ↔ colHit x a b := by
  simp only [cross,colHit,first,second,adj,ite_true,bits_point,bits_line,decide_eq_true_eq]

def target (x : Word) := ∃ p∈pts x, ∃ l∈lines x,inc p l
theorem classifies {x : Word} {a b : V} (ne : a≠b) (d : Bool) :
    truth (bits x) (merged d a b)=true ↔ target x ∨ (if d then colHit x a b else rowHit x a b) := by
  rw [merged_spec _ _ _ ne]
  cases d <;> simp [edge_primal,edge_dual,cross_primal,cross_dual,target]

def seeds {α} (data : α → Word) : Set (Set α) := {∅,Set.univ} ∪ Set.range
  (fun i : Input => {k | bits (data k) i=true})
def hard {α} (data : α → Word) (labels : Set α) := ∀ gs : List (Set α),
  gs.length≤63 → legal (seeds data) gs → labels ∉ bank (seeds data) gs

theorem excludes {α} {data : α → Word} {labels : Set α} (h : hard data labels)
    (f : Form) (cost : gates f≤63) : ¬ ∀ k, k∈labels ↔ truth (bits (data k)) f=true := by
  intro answers
  let raw := fun (i : Input) => {k | bits (data k) i=true}
  obtain ⟨gs,len,valid,out⟩ := compile raw (seeds data) (fun i => Or.inr ⟨i,rfl⟩)
    (Or.inl (by simp)) f [] (by simp [legal])
  have eq : labels=value raw f := Set.ext (fun k => (answers k).trans (semantics (fun r i => bits (data r) i) f k).symm)
  apply h gs (len.trans cost) (by simpa using valid)
  simpa [eq] using out

theorem generic_no_edge {x : Word} (g : Generic x) : ¬target x := by
  rintro ⟨p,hp,l,hl,e⟩; exact g.1 p hp l hl e

/-- A hard sample requires a distinguishing negative for every point-pair merger
and for every line-pair merger, regardless of duplicate rows and their encoding. -/
theorem demands_mergers {α} (data : α → Word) (labels : Set α) (h : hard data labels)
    (yes : ∀ k∈labels,target (data k)) (no : ∀ k∉labels,Generic (data k)) (a b : V) (ne : a≠b) :
    (∃ k∉labels,rowHit (data k) a b) ∧ (∃ k∉labels,colHit (data k) a b) := by
  have find (d : Bool) : ∃ k∉labels,(if d then colHit (data k) a b else rowHit (data k) a b) := by
    classical
    by_contra! fail
    apply excludes h (merged d a b) (merged_cost d a b ne).le
    intro k
    rw [classifies ne d]
    by_cases hk : k∈labels
    · exact ⟨fun _ => Or.inl (yes k hk),fun _ => hk⟩
    · exact ⟨fun bad => False.elim (hk bad),fun hit => False.elim (hit.elim (generic_no_edge (no k hk)) (fail k hk))⟩
  exact ⟨by simpa using find false,by simpa using find true⟩

theorem more_than_five {α} (data : α → Word) (labels : Set α) (h : hard data labels)
    (yes : ∀ k∈labels,target (data k)) (no : ∀ k∉labels,Generic (data k)) :
    ¬ ∃ r : Fin 5 → Word, (∀ i,Generic (r i)) ∧ ∀ k∉labels,∃ i,data k=r i := by
  rintro ⟨r,gen,all⟩
  rcases five_insufficient r gen with ⟨a,b,ne,miss⟩ | ⟨a,b,ne,miss⟩
  · obtain ⟨k,hk,hit⟩ := (demands_mergers data labels h yes no a b ne).1
    obtain ⟨i,eq⟩ := all k hk; exact miss i (eq ▸ hit)
  · obtain ⟨k,hk,hit⟩ := (demands_mergers data labels h yes no a b ne).2
    obtain ⟨i,eq⟩ := all k hk; exact miss i (eq ▸ hit)

end PEqualNP.Research.NecessarySamples

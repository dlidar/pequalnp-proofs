"""Build 64 short endpoint-matching certificates for the integral rectangle dual."""
from pathlib import Path
import json
from merged_stars import edges
W=Path(__file__).resolve().parent
tests=json.loads((W/'design.json').read_text())
weights=[int(v) for v in json.loads((W/'cover-dual.json').read_text())]
tokens=[e for e,v in zip(edges,weights) for _ in range(v)]
cert=[]
for s in range(64):
    p=l=(1<<13)-1
    for i,(P,L) in enumerate(tests):
        if s>>i&1:p&=~P
        else:l&=~L
    indices=[j for j,(a,b) in enumerate(tokens) if p>>a&1 and l>>b&1]
    used={}
    def match(k,visited):
        a,b=tokens[k]
        for v in (a,b+13):
            if v in visited:continue
            visited.add(v)
            if v not in used or match(used[v],visited):
                used[v]=k
                return True
        return False
    assert all(match(k,set()) for k in indices)
    cert.append(sum(1<<k for i,k in used.items() if i>=13))
def literal(ns):return '['+', '.join(map(str,ns))+']'
s='''import PEqualNP.Research.SixRowCircuit

namespace PEqualNP.Research.IntegralCover
open Finset PEqualNP.Research.CapBoundary
abbrev Token := Fin 49
abbrev Partition := BitVec 6
def testP (i : Fin 6) : BitVec 13 := ('''+literal([p for p,l in tests])+''' : List (BitVec 13)).getD i.val 0
def testL (i : Fin 6) : BitVec 13 := ('''+literal([l for p,l in tests])+''' : List (BitVec 13)).getD i.val 0
def pt (t : Token) : V := ('''+literal([p for p,l in tokens])+''' : List V).getD t.val 0
def ln (t : Token) : V := ('''+literal([l for p,l in tokens])+''' : List V).getD t.val 0
def right (s : Partition) : BitVec 49 := ('''+literal(cert)+''' : List (BitVec 49)).getD s.toNat 0

def allowed (s : Partition) := univ.filter fun t : Token => ∀ i : Fin 6,
  if s.getLsbD i.val then !(testP i).getLsbD (pt t).val else !(testL i).getLsbD (ln t).val

def charge (s : Partition) (t : Token) : V ⊕ V :=
  if (right s).getLsbD t.val then Sum.inr (ln t) else Sum.inl (pt t)

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem token_incidence : ∀ t : Token, inc (pt t) (ln t) := by decide +kernel

'''
# Small, separate reflected obligations keep the recheck bounded.
for i in range(64):
    s+=f'private theorem check{i} : ((allowed {i}).image (charge {i})).card=(allowed {i}).card := by decide +kernel\n'
s+='''theorem injective_on (s : Partition) : Set.InjOn (charge s) (allowed s : Finset Token) := by
  apply Finset.injOn_of_card_image_eq
  have h : s.toNat < 64 := s.isLt
  interval_cases eq : s.toNat
'''+''.join(f'  · have e : s={i} := BitVec.eq_of_toNat_eq eq\n    exact e ▸ check{i}\n' for i in range(64))+'''
def safe (P L : Finset V) := ∀ i : Fin 6,
  (∀ p∈P,(testP i).getLsbD p.val=false) ∨ (∀ l∈L,(testL i).getLsbD l.val=false)

def tokens (P L : Finset V) := univ.filter fun t : Token => pt t∈P ∧ ln t∈L

theorem rectangle (P L : Finset V) (h : safe P L) : (tokens P L).card ≤ P.card+L.card := by
  classical
  let v := fun i : Fin 6 => decide (∀ p∈P,(testP i).getLsbD p.val=false)
  let s : Partition := (BitVec.ofBoolListLE (List.ofFn v)).cast (by simp)
  have bit (i : Fin 6) : s.getLsbD i.val = v i := by
    simp only [s,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have sub : tokens P L ⊆ allowed s := by
    intro t ht
    obtain ⟨hp,hl⟩ := (mem_filter.mp ht).2
    apply mem_filter.mpr;refine ⟨mem_univ _,?_⟩
    intro i
    rw [bit i]
    by_cases left : ∀ p∈P,(testP i).getLsbD p.val=false
    · rw [show v i=true from decide_eq_true left,left _ hp];simp
    · have rest := (h i).resolve_left left
      rw [show v i=false from decide_eq_false left,rest _ hl];simp
  have inj := (injective_on s).mono (show (tokens P L : Set Token) ⊆ allowed s from sub)
  have dest : (tokens P L).image (charge s) ⊆ P.disjSum L := by
    rintro _ hi;obtain ⟨t,ht,rfl⟩ := mem_image.mp hi
    obtain ⟨hp,hl⟩ := (mem_filter.mp ht).2
    unfold charge;split <;> simp [hp,hl]
  have n := card_le_card dest
  rwa [card_image_of_injOn inj,card_disjSum] at n

theorem raw_points : ∀ p : V, (∀ i,(testP i).getLsbD p.val=false) →
    (univ.filter fun t : Token => pt t=p).card ≤ 1 := by decide +kernel
theorem raw_lines : ∀ l : V, (∀ i,(testL i).getLsbD l.val=false) →
    (univ.filter fun t : Token => ln t=l).card ≤ 1 := by decide +kernel

/-- Every cover of the flags by safe blocks pays at least 49 leaves, allowing
individual raw vertices as well as point-by-line rectangles. -/
theorem cover {m : ℕ} (block : Fin m → Finset Token) (cost : Fin m → ℕ)
    (all : ∀ t : Token,∃ j,t∈block j) (each : ∀ j,(block j).card ≤ cost j) :
    49 ≤ ∑ j,cost j := by
  have sub : (univ : Finset Token) ⊆ univ.biUnion block := by
    intro t _;obtain ⟨j,hj⟩ := all t;exact mem_biUnion.mpr ⟨j,mem_univ _,hj⟩
  exact (by simpa using card_le_card sub : 49 ≤ (univ.biUnion block).card) |>.trans
    ((card_biUnion_le).trans (sum_le_sum (fun j _ => each j)))


inductive Block where
  | rectangle (P L : Finset V)
  | point (p : V)
  | line (l : V)

def Block.hits (b : Block) (p l : V) : Prop := match b with
  | .rectangle P L => p∈P ∧ l∈L
  | .point i => p=i
  | .line j => l=j

def Block.valid (b : Block) : Prop := match b with
  | .rectangle P L => safe P L
  | .point p => ∀ i,(testP i).getLsbD p.val=false
  | .line l => ∀ i,(testL i).getLsbD l.val=false

def Block.leaves (b : Block) : ℕ := match b with
  | .rectangle P L => P.card+L.card
  | .point _ | .line _ => 1

def Block.toks : Block → Finset Token
  | .rectangle P L => tokens P L
  | .point p => univ.filter fun t => pt t=p
  | .line l => univ.filter fun t => ln t=l

theorem mem_toks (t : Token) (b : Block) : t∈b.toks ↔ b.hits (pt t) (ln t) := by
  cases b <;> simp [Block.toks,Block.hits,tokens]

theorem restricted_lower {m} (blocks : Fin m → Block) (valid : ∀ j,(blocks j).valid)
    (flags : ∀ p l : V, inc p l → ∃ j,(blocks j).hits p l) :
    48 ≤ (∑ j,(blocks j).leaves)-1 := by
  classical
  have ok (b : Block) (h : b.valid) : b.toks.card ≤ b.leaves := by
    cases b with
    | rectangle P L => exact rectangle P L h
    | point p => exact raw_points p h
    | line l => exact raw_lines l h
  have all (t : Token) : ∃ j,t∈(blocks j).toks := by
    obtain ⟨j,h⟩ := flags _ _ (token_incidence t)
    exact ⟨j,(mem_toks t _).mpr h⟩
  have cost := cover (fun j => (blocks j).toks) (fun j => (blocks j).leaves) all (fun j => ok _ (valid j))
  omega

end PEqualNP.Research.IntegralCover
'''
(W/'IntegralCover.lean').write_text(s)

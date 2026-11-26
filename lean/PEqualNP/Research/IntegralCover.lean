import PEqualNP.Research.SixRowCircuit

namespace PEqualNP.Research.IntegralCover
open Finset PEqualNP.Research.CapBoundary
abbrev Token := Fin 49
abbrev Partition := BitVec 6
def testP (i : Fin 6) : BitVec 13 := ([4628, 1168, 104, 2368, 284, 5122] : List (BitVec 13)).getD i.val 0
def testL (i : Fin 6) : BitVec 13 := ([1184, 4133, 6402, 531, 3584, 340] : List (BitVec 13)).getD i.val 0
def pt (t : Token) : V := ([0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12] : List V).getD t.val 0
def ln (t : Token) : V := ([0, 0, 1, 5, 11, 2, 6, 12, 0, 0, 2, 3, 7, 1, 4, 8, 8, 4, 4, 5, 9, 5, 6, 10, 10, 4, 6, 7, 11, 5, 5, 7, 8, 12, 0, 8, 9, 1, 1, 9, 10, 2, 8, 10, 11, 11, 9, 12, 12] : List V).getD t.val 0
def right (s : Partition) : BitVec 49 := ([0, 2048, 0, 2684356608, 0, 0, 140737488355328, 11274289152, 0, 2048, 2304, 6408, 137438953472, 137438953472, 140737488355330, 6, 0, 8388608, 0, 10485760, 17592186044416, 26388413284352, 158329674399744, 26388279066632, 0, 549755813888, 17179869184, 524290, 687194767376, 1786840612880, 211123412402196, 14, 0, 67110912, 1088, 2688551936, 32768, 2214592512, 2203318223040, 2214592512000, 67239936, 201459712, 134464, 662784, 67166208, 100663296, 17179869280, 0, 0, 146800640, 0, 2199037935616, 21990299664384, 30786526904320, 24189255811072, 32985348833280, 68288512, 202506240, 17181048832, 1703936, 34460401664, 234881024, 51539607552, 0] : List (BitVec 49)).getD s.toNat 0

def allowed (s : Partition) := univ.filter fun t : Token => ∀ i : Fin 6,
  if s.getLsbD i.val then !(testP i).getLsbD (pt t).val else !(testL i).getLsbD (ln t).val

def charge (s : Partition) (t : Token) : V ⊕ V :=
  if (right s).getLsbD t.val then Sum.inr (ln t) else Sum.inl (pt t)

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem token_incidence : ∀ t : Token, inc (pt t) (ln t) := by decide +kernel

private theorem check0 : ((allowed 0).image (charge 0)).card=(allowed 0).card := by decide +kernel
private theorem check1 : ((allowed 1).image (charge 1)).card=(allowed 1).card := by decide +kernel
private theorem check2 : ((allowed 2).image (charge 2)).card=(allowed 2).card := by decide +kernel
private theorem check3 : ((allowed 3).image (charge 3)).card=(allowed 3).card := by decide +kernel
private theorem check4 : ((allowed 4).image (charge 4)).card=(allowed 4).card := by decide +kernel
private theorem check5 : ((allowed 5).image (charge 5)).card=(allowed 5).card := by decide +kernel
private theorem check6 : ((allowed 6).image (charge 6)).card=(allowed 6).card := by decide +kernel
private theorem check7 : ((allowed 7).image (charge 7)).card=(allowed 7).card := by decide +kernel
private theorem check8 : ((allowed 8).image (charge 8)).card=(allowed 8).card := by decide +kernel
private theorem check9 : ((allowed 9).image (charge 9)).card=(allowed 9).card := by decide +kernel
private theorem check10 : ((allowed 10).image (charge 10)).card=(allowed 10).card := by decide +kernel
private theorem check11 : ((allowed 11).image (charge 11)).card=(allowed 11).card := by decide +kernel
private theorem check12 : ((allowed 12).image (charge 12)).card=(allowed 12).card := by decide +kernel
private theorem check13 : ((allowed 13).image (charge 13)).card=(allowed 13).card := by decide +kernel
private theorem check14 : ((allowed 14).image (charge 14)).card=(allowed 14).card := by decide +kernel
private theorem check15 : ((allowed 15).image (charge 15)).card=(allowed 15).card := by decide +kernel
private theorem check16 : ((allowed 16).image (charge 16)).card=(allowed 16).card := by decide +kernel
private theorem check17 : ((allowed 17).image (charge 17)).card=(allowed 17).card := by decide +kernel
private theorem check18 : ((allowed 18).image (charge 18)).card=(allowed 18).card := by decide +kernel
private theorem check19 : ((allowed 19).image (charge 19)).card=(allowed 19).card := by decide +kernel
private theorem check20 : ((allowed 20).image (charge 20)).card=(allowed 20).card := by decide +kernel
private theorem check21 : ((allowed 21).image (charge 21)).card=(allowed 21).card := by decide +kernel
private theorem check22 : ((allowed 22).image (charge 22)).card=(allowed 22).card := by decide +kernel
private theorem check23 : ((allowed 23).image (charge 23)).card=(allowed 23).card := by decide +kernel
private theorem check24 : ((allowed 24).image (charge 24)).card=(allowed 24).card := by decide +kernel
private theorem check25 : ((allowed 25).image (charge 25)).card=(allowed 25).card := by decide +kernel
private theorem check26 : ((allowed 26).image (charge 26)).card=(allowed 26).card := by decide +kernel
private theorem check27 : ((allowed 27).image (charge 27)).card=(allowed 27).card := by decide +kernel
private theorem check28 : ((allowed 28).image (charge 28)).card=(allowed 28).card := by decide +kernel
private theorem check29 : ((allowed 29).image (charge 29)).card=(allowed 29).card := by decide +kernel
private theorem check30 : ((allowed 30).image (charge 30)).card=(allowed 30).card := by decide +kernel
private theorem check31 : ((allowed 31).image (charge 31)).card=(allowed 31).card := by decide +kernel
private theorem check32 : ((allowed 32).image (charge 32)).card=(allowed 32).card := by decide +kernel
private theorem check33 : ((allowed 33).image (charge 33)).card=(allowed 33).card := by decide +kernel
private theorem check34 : ((allowed 34).image (charge 34)).card=(allowed 34).card := by decide +kernel
private theorem check35 : ((allowed 35).image (charge 35)).card=(allowed 35).card := by decide +kernel
private theorem check36 : ((allowed 36).image (charge 36)).card=(allowed 36).card := by decide +kernel
private theorem check37 : ((allowed 37).image (charge 37)).card=(allowed 37).card := by decide +kernel
private theorem check38 : ((allowed 38).image (charge 38)).card=(allowed 38).card := by decide +kernel
private theorem check39 : ((allowed 39).image (charge 39)).card=(allowed 39).card := by decide +kernel
private theorem check40 : ((allowed 40).image (charge 40)).card=(allowed 40).card := by decide +kernel
private theorem check41 : ((allowed 41).image (charge 41)).card=(allowed 41).card := by decide +kernel
private theorem check42 : ((allowed 42).image (charge 42)).card=(allowed 42).card := by decide +kernel
private theorem check43 : ((allowed 43).image (charge 43)).card=(allowed 43).card := by decide +kernel
private theorem check44 : ((allowed 44).image (charge 44)).card=(allowed 44).card := by decide +kernel
private theorem check45 : ((allowed 45).image (charge 45)).card=(allowed 45).card := by decide +kernel
private theorem check46 : ((allowed 46).image (charge 46)).card=(allowed 46).card := by decide +kernel
private theorem check47 : ((allowed 47).image (charge 47)).card=(allowed 47).card := by decide +kernel
private theorem check48 : ((allowed 48).image (charge 48)).card=(allowed 48).card := by decide +kernel
private theorem check49 : ((allowed 49).image (charge 49)).card=(allowed 49).card := by decide +kernel
private theorem check50 : ((allowed 50).image (charge 50)).card=(allowed 50).card := by decide +kernel
private theorem check51 : ((allowed 51).image (charge 51)).card=(allowed 51).card := by decide +kernel
private theorem check52 : ((allowed 52).image (charge 52)).card=(allowed 52).card := by decide +kernel
private theorem check53 : ((allowed 53).image (charge 53)).card=(allowed 53).card := by decide +kernel
private theorem check54 : ((allowed 54).image (charge 54)).card=(allowed 54).card := by decide +kernel
private theorem check55 : ((allowed 55).image (charge 55)).card=(allowed 55).card := by decide +kernel
private theorem check56 : ((allowed 56).image (charge 56)).card=(allowed 56).card := by decide +kernel
private theorem check57 : ((allowed 57).image (charge 57)).card=(allowed 57).card := by decide +kernel
private theorem check58 : ((allowed 58).image (charge 58)).card=(allowed 58).card := by decide +kernel
private theorem check59 : ((allowed 59).image (charge 59)).card=(allowed 59).card := by decide +kernel
private theorem check60 : ((allowed 60).image (charge 60)).card=(allowed 60).card := by decide +kernel
private theorem check61 : ((allowed 61).image (charge 61)).card=(allowed 61).card := by decide +kernel
private theorem check62 : ((allowed 62).image (charge 62)).card=(allowed 62).card := by decide +kernel
private theorem check63 : ((allowed 63).image (charge 63)).card=(allowed 63).card := by decide +kernel
theorem injective_on (s : Partition) : Set.InjOn (charge s) (allowed s : Finset Token) := by
  apply Finset.injOn_of_card_image_eq
  have h : s.toNat < 64 := s.isLt
  interval_cases eq : s.toNat
  · have e : s=0 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check0
  · have e : s=1 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check1
  · have e : s=2 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check2
  · have e : s=3 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check3
  · have e : s=4 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check4
  · have e : s=5 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check5
  · have e : s=6 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check6
  · have e : s=7 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check7
  · have e : s=8 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check8
  · have e : s=9 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check9
  · have e : s=10 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check10
  · have e : s=11 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check11
  · have e : s=12 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check12
  · have e : s=13 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check13
  · have e : s=14 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check14
  · have e : s=15 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check15
  · have e : s=16 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check16
  · have e : s=17 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check17
  · have e : s=18 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check18
  · have e : s=19 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check19
  · have e : s=20 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check20
  · have e : s=21 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check21
  · have e : s=22 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check22
  · have e : s=23 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check23
  · have e : s=24 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check24
  · have e : s=25 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check25
  · have e : s=26 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check26
  · have e : s=27 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check27
  · have e : s=28 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check28
  · have e : s=29 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check29
  · have e : s=30 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check30
  · have e : s=31 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check31
  · have e : s=32 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check32
  · have e : s=33 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check33
  · have e : s=34 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check34
  · have e : s=35 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check35
  · have e : s=36 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check36
  · have e : s=37 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check37
  · have e : s=38 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check38
  · have e : s=39 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check39
  · have e : s=40 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check40
  · have e : s=41 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check41
  · have e : s=42 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check42
  · have e : s=43 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check43
  · have e : s=44 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check44
  · have e : s=45 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check45
  · have e : s=46 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check46
  · have e : s=47 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check47
  · have e : s=48 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check48
  · have e : s=49 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check49
  · have e : s=50 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check50
  · have e : s=51 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check51
  · have e : s=52 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check52
  · have e : s=53 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check53
  · have e : s=54 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check54
  · have e : s=55 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check55
  · have e : s=56 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check56
  · have e : s=57 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check57
  · have e : s=58 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check58
  · have e : s=59 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check59
  · have e : s=60 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check60
  · have e : s=61 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check61
  · have e : s=62 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check62
  · have e : s=63 := BitVec.eq_of_toNat_eq eq
    exact e ▸ check63

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

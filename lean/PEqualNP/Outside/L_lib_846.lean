import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_846_aux

abbrev Data := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ


def Valid (t : Data) : Prop :=
  0 ≤ t.2.2.1 ∧ 0 ≤ t.2.2.2.1 ∧ 0 ≤ t.2.2.2.2.1 ∧ 0 ≤ t.2.2.2.2.2 ∧
  t.2.2.1 + t.2.2.2.1 ≤ t.1 ∧ t.2.2.2.2.1 + t.2.2.2.2.2 ≤ t.1 ∧ t.2.2.1 + t.2.2.2.2.1 ≤ t.2.1 ∧ t.2.2.2.1 + t.2.2.2.2.2 ≤ t.2.1 ∧
  (t.2.2.1+t.2.2.2.1)%2=t.1%2 ∧ (t.2.2.1+t.2.2.2.2.1)%2=t.2.1%2 ∧
  (t.2.2.1+t.2.2.2.2.2)%2=(t.1+t.2.1)%2

def Inside (t : Data) (u v : ℤ) : Prop :=
  0 ≤ u ∧ u ≤ t.1 ∧ 0 ≤ v ∧ v ≤ t.2.1 ∧ (u+v)%2=t.2.2.1%2 ∧
  t.2.2.1 ≤ u+v ∧ t.2.2.2.1 ≤ t.1-u+v ∧ t.2.2.2.2.1 ≤ u+t.2.1-v ∧ t.2.2.2.2.2 ≤ t.1-u+t.2.1-v

def add (t h : Data) : Data :=
  ⟨t.1+h.1,t.2.1+h.2.1,t.2.2.1+h.2.2.1,t.2.2.2.1+h.2.2.2.1,t.2.2.2.2.1+h.2.2.2.2.1,t.2.2.2.2.2+h.2.2.2.2.2⟩

theorem add_valid (t h : Data) (ht : Valid t) (hh : Valid h) : Valid (add t h) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  rcases hh with ⟨kd,ke,kf,kg,kde,kfg,kdf,keg,kx,ky,kz⟩
  unfold Valid add
  dsimp only
  omega

theorem inside_add {t h : Data} {u v x y : ℤ} (ht : Inside t u v) (hh : Inside h x y) :
    Inside (add t h) (u+x) (v+y) := by
  rcases ht with ⟨_,_,_,_,_,_,_,_,_⟩
  rcases hh with ⟨_,_,_,_,_,_,_,_,_⟩
  unfold Inside add
  dsimp only
  omega

def bit (a : ℕ) (s : Bool) : ℤ := ((a+s.toNat)%2 : ℕ)

def box (a b : ℕ) (s : Bool) : Data :=
  ⟨a,b,bit 0 s,bit a s,bit b s,bit (a+b) s⟩

theorem box_valid {a b : ℕ} (s : Bool) (ha : 0<a) (hb : 0<b) : Valid (box a b s) := by
  cases s <;> simp only [Valid,box,bit,Bool.toNat_false,Bool.toNat_true,Nat.zero_add,Nat.add_zero] <;>
    push_cast
  all_goals simp only [true_and, zero_add, Int.reduceAdd, Int.reduceMod, Int.reduceLE] at *
  all_goals repeat' constructor
  all_goals omega

def Splits (h : Data) := ∀ t, Valid t → 0 < t.1 → 0 < t.2.1 → ∀ u v, Inside (add t h) u v →
  ∃ x y, Inside h x y ∧ Inside t (u-x) (v-y)

theorem add_assoc (t h k : Data) : add t (add h k) = add (add t h) k := by
  cases t; cases h; cases k; simp [add,Int.add_assoc]

theorem splits_add {h k : Data} (vh : Valid h) (sh : Splits h) (sk : Splits k) :
    Splits (add h k) := by
  intro t vt pa pb u v hit
  have hA : 0 ≤ h.1 := by rcases vh with ⟨_,_,_,_,_,_,_,_,_,_,_⟩; omega
  have hB : 0 ≤ h.2.1 := by rcases vh with ⟨_,_,_,_,_,_,_,_,_,_,_⟩; omega
  rw [add_assoc] at hit
  obtain ⟨u₂,v₂,loc₂,mid⟩ := sk _ (add_valid _ _ vt vh) (by change 0<t.1+h.1; omega) (by change 0<t.2.1+h.2.1; omega) _ _ hit
  obtain ⟨u₁,v₁,loc₁,old⟩ := sh _ vt pa pb _ _ mid
  refine ⟨u₁+u₂,v₁+v₂,inside_add loc₁ loc₂,?_⟩
  convert old using 1 <;> ring

theorem box_add_left (a b : ℕ) (s : Bool) :
    box (a+2) b s = add (box a b s) ⟨2,0,0,0,0,0⟩ := by
  cases s <;> simp [box,bit,add] <;> omega

theorem box_add_right (a b : ℕ) (s : Bool) :
    box a (b+2) s = add (box a b s) ⟨0,2,0,0,0,0⟩ := by
  cases s <;> simp [box,bit,add] <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem G200 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨2,0,0,0,0,0⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-2) (v-0) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  unfold Inside
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem G020 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨0,2,0,0,0,0⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-0) (v-2) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  unfold Inside
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem G110 (t : Data) (ht : Valid t) (u v : ℤ) (h : Inside (add t ⟨1,1,0,1,1,0⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-1) (v-1) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  unfold Inside
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem G111 (t : Data) (ht : Valid t) (u v : ℤ) (h : Inside (add t ⟨1,1,1,0,0,1⟩) u v) :
    Inside t (u-0) (v-1) ∨
    Inside t (u-1) (v-0) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  unfold Inside
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H120 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨1,2,0,1,0,1⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-0) (v-2) ∨
    Inside t (u-1) (v-1) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 1 ≤ t.1+1-u
  · by_cases hcut1 : 2 ≤ u+t.2.1+2-v-t.2.2.2.2.1
    · by_cases hcut2 : 2 ≤ t.2.1+2-v
      · by_cases hcut3 : 3 ≤ t.1+1-u+t.2.1+2-v-t.2.2.2.2.2
        · left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · right
          left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd hf hg hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3; omega
      · right
        left
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
        · clear pa hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hg hde hfg heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0; omega
        · clear pa pb hd he hf hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2; omega
    · right
      left
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1; omega
      · clear pa pb he hf hg hde hfg heg hx hy hz hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg heg hx hy hz hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1; omega
  · right
    right
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb hd he hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4; omega
    · clear pa pb hd he hf hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0; omega
    · clear pa pb hd he hf hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H121 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨1,2,1,0,1,0⟩) u v) :
    Inside t (u-0) (v-1) ∨
    Inside t (u-1) (v-0) ∨
    Inside t (u-1) (v-2) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 1 ≤ u
  · by_cases hcut1 : 2 ≤ t.1+1-u+v-t.2.2.2.1
    · by_cases hcut2 : 2 ≤ v
      · by_cases hcut3 : 3 ≤ u+v-t.2.2.1
        · right
          right
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3; omega
        · left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hg hde hfg heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
      · right
        left
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
        · clear pa pb he hf hg hde hfg heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · right
      left
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hde hfg hdf hx hy hu hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf hx hy hu hv hV h1 h2 h3 h4 hcut0; omega
  · left
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd he hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0; omega
    · clear pa pb he hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0; omega
    · clear pa pb hd he hg hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H210 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨2,1,0,0,1,1⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-1) (v-1) ∨
    Inside t (u-2) (v-0) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 1 ≤ t.2.1+1-v
  · by_cases hcut1 : 2 ≤ t.1+2-u+v-t.2.2.2.1
    · by_cases hcut2 : 2 ≤ t.1+2-u
      · by_cases hcut3 : 3 ≤ t.1+2-u+t.2.1+1-v-t.2.2.2.2.2
        · left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · right
          left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hg hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3; omega
      · right
        right
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · clear pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
        · clear pa pb hd he hf hde hdf heg hx hy hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2; omega
    · right
      right
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb he hf hg hfg hdf heg hx hy hz hu hU hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hfg hdf heg hx hy hz hu hU hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1; omega
  · right
    left
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb hd he hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4; omega
    · clear pa pb hd he hf hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3; omega
    · clear pa pb hd hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hg hde hfg heg hx hy hz hpar hu hU hv hV h1 h2 h4; omega
    · clear pa pb hd he hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H211 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨2,1,1,1,0,0⟩) u v) :
    Inside t (u-0) (v-1) ∨
    Inside t (u-1) (v-0) ∨
    Inside t (u-2) (v-1) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 1 ≤ v
  · by_cases hcut1 : 2 ≤ t.1+2-u+t.2.1+1-v-t.2.2.2.2.2
    · by_cases hcut2 : 2 ≤ t.1+2-u
      · by_cases hcut3 : 3 ≤ t.1+2-u+v-t.2.2.2.1
        · left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
        · right
          left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb he hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
      · right
        right
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · clear pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd hf hg hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
    · right
      right
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb hd he hg hde hdf heg hx hy hu hU hv h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hdf heg hx hy hu hU hv h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1; omega
  · right
    left
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0; omega
    · clear pa pb he hf hg hde hfg heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h3 h4; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H220 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨2,2,0,0,0,0⟩) u v) :
    Inside t (u-0) (v-0) ∨
    Inside t (u-0) (v-2) ∨
    Inside t (u-1) (v-1) ∨
    Inside t (u-2) (v-0) ∨
    Inside t (u-2) (v-2) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 2 ≤ t.1+2-u+v-t.2.2.2.1
  · by_cases hcut1 : 2 ≤ u+t.2.1+2-v-t.2.2.2.2.1
    · by_cases hcut2 : 2 ≤ t.1+2-u
      · by_cases hcut3 : 2 ≤ t.2.1+2-v
        · by_cases hcut4 : 4 ≤ t.1+2-u+t.2.1+2-v-t.2.2.2.2.2
          · left
            refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · by_cases hcut5 : 2 ≤ t.1+2-u+t.2.1+2-v-t.2.2.2.2.2
            · right
              left
              refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4 hcut5; omega
              · clear pa pb hd hf hg hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · right
              right
              right
              right
              refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
              · clear pa pb hd he hg hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4 hcut5; omega
              · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4 hcut5; omega
              · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3 hcut4 hcut5; omega
        · by_cases hcut4 : 2 ≤ t.1+2-u+t.2.1+2-v-t.2.2.2.2.2
          · right
            left
            refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
            · clear pa hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hg hde hfg heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut4; omega
            · clear pa pb hd he hf hde hfg hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · right
            right
            right
            right
            refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · clear pa pb hd he hg hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
            · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3 hcut4; omega
      · by_cases hcut3 : 2 ≤ v
        · right
          right
          right
          right
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd hf hg hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3; omega
        · right
          right
          left
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
          · clear pa pb hd hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut3; omega
          · clear pa pb hd hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
    · right
      left
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hde hdf heg hx hy hu hU hv h1 h2 h3 h4 hcut0; omega
      · clear pa pb he hf hg hde hfg heg hx hy hz hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg heg hx hy hz hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hdf heg hx hy hu hU hv h1 h2 h3 h4 hcut0; omega
  · right
    right
    right
    left
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb he hf hg hfg hdf heg hx hy hz hu hU hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hde hfg hdf hx hy hu hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hfg hdf heg hx hy hz hu hU hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0; omega
    · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf hx hy hu hv hV h1 h2 h3 h4; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem H221 (t : Data) (ht : Valid t) (pa : 0<t.1) (pb : 0<t.2.1) (u v : ℤ) (h : Inside (add t ⟨2,2,1,1,1,1⟩) u v) :
    Inside t (u-0) (v-1) ∨
    Inside t (u-1) (v-0) ∨
    Inside t (u-1) (v-2) ∨
    Inside t (u-2) (v-1) := by
  rcases ht with ⟨hd,he,hf,hg,hde,hfg,hdf,heg,hx,hy,hz⟩
  unfold Inside add at h
  dsimp only at h
  rcases h with ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
  by_cases hcut0 : 1 ≤ v
  · by_cases hcut1 : 1 ≤ t.2.1+2-v
    · by_cases hcut2 : 3 ≤ t.1+2-u+v-t.2.2.2.1
      · by_cases hcut3 : 3 ≤ t.1+2-u+t.2.1+2-v-t.2.2.2.2.2
        · by_cases hcut4 : 2 ≤ t.1+2-u
          · left
            refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4; omega
          · right
            right
            right
            refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · clear pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3 hcut4; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3 hcut4; omega
            · clear pa pb hd hf hg hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3 hcut4; omega
            · clear pa pb hd he hf hde hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
            · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut4; omega
        · right
          right
          right
          refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · clear pa pb hd he hg hde hdf heg hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2 hcut3; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2 hcut3; omega
          · clear pa pb hd he hg hde heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut3; omega
          · clear pa pb hd he hf hg hde hdf heg hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
          · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2 hcut3; omega
      · right
        right
        right
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · clear pa pb he hf hg hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0 hcut2; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hg hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0 hcut1 hcut2; omega
        · clear pa pb hd he hf hde hdf hx hy hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
        · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1 hcut2; omega
    · right
      right
      left
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · clear pa pb hd he hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0; omega
      · clear pa pb hd he hf hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0; omega
      · clear pa pb hd hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0 hcut1; omega
      · clear pa pb hd he hg hde hfg heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0; omega
      · clear pa pb hd he hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h4 hcut0 hcut1; omega
      · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h2 h3 hcut0 hcut1; omega
  · right
    left
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · clear pa pb he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd hf hde hfg hdf hx hy hz hpar hu hU hv hV h1 h2 h3 h4; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hu hU hv hV h1 h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h2 h3 h4 hcut0; omega
    · clear pa pb hd he hf hg hde hfg hdf heg hx hy hz hpar hu hU hv hV h1 h3 h4 hcut0; omega
    · clear pa pb he hf hg hde hfg heg hx hy hz hpar hu hU hv hV h2 h3 h4; omega
    · clear pa pb hd hf hg hde hfg hdf hx hy hz hpar hu hU hv hV h1 h3 h4; omega

theorem S200 : Splits ⟨2,0,0,0,0,0⟩ := by
  intro t ht pa pb u v h
  rcases G200 t ht pa pb u v h with z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨2,0,by unfold Inside; decide,z⟩
theorem S020 : Splits ⟨0,2,0,0,0,0⟩ := by
  intro t ht pa pb u v h
  rcases G020 t ht pa pb u v h with z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨0,2,by unfold Inside; decide,z⟩
theorem S110 : Splits ⟨1,1,0,1,1,0⟩ := by
  intro t ht pa pb u v h
  rcases G110 t ht u v h with z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨1,1,by unfold Inside; decide,z⟩
theorem S111 : Splits ⟨1,1,1,0,0,1⟩ := by
  intro t ht pa pb u v h
  rcases G111 t ht u v h with z | z
  · exact ⟨0,1,by unfold Inside; decide,z⟩
  · exact ⟨1,0,by unfold Inside; decide,z⟩
theorem S120 : Splits ⟨1,2,0,1,0,1⟩ := by
  intro t ht pa pb u v h
  rcases H120 t ht pa pb u v h with z | z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨0,2,by unfold Inside; decide,z⟩
  · exact ⟨1,1,by unfold Inside; decide,z⟩
theorem S121 : Splits ⟨1,2,1,0,1,0⟩ := by
  intro t ht pa pb u v h
  rcases H121 t ht pa pb u v h with z | z | z
  · exact ⟨0,1,by unfold Inside; decide,z⟩
  · exact ⟨1,0,by unfold Inside; decide,z⟩
  · exact ⟨1,2,by unfold Inside; decide,z⟩
theorem S210 : Splits ⟨2,1,0,0,1,1⟩ := by
  intro t ht pa pb u v h
  rcases H210 t ht pa pb u v h with z | z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨1,1,by unfold Inside; decide,z⟩
  · exact ⟨2,0,by unfold Inside; decide,z⟩
theorem S211 : Splits ⟨2,1,1,1,0,0⟩ := by
  intro t ht pa pb u v h
  rcases H211 t ht pa pb u v h with z | z | z
  · exact ⟨0,1,by unfold Inside; decide,z⟩
  · exact ⟨1,0,by unfold Inside; decide,z⟩
  · exact ⟨2,1,by unfold Inside; decide,z⟩
theorem S220 : Splits ⟨2,2,0,0,0,0⟩ := by
  intro t ht pa pb u v h
  rcases H220 t ht pa pb u v h with z | z | z | z | z
  · exact ⟨0,0,by unfold Inside; decide,z⟩
  · exact ⟨0,2,by unfold Inside; decide,z⟩
  · exact ⟨1,1,by unfold Inside; decide,z⟩
  · exact ⟨2,0,by unfold Inside; decide,z⟩
  · exact ⟨2,2,by unfold Inside; decide,z⟩
theorem S221 : Splits ⟨2,2,1,1,1,1⟩ := by
  intro t ht pa pb u v h
  rcases H221 t ht pa pb u v h with z | z | z | z
  · exact ⟨0,1,by unfold Inside; decide,z⟩
  · exact ⟨1,0,by unfold Inside; decide,z⟩
  · exact ⟨1,2,by unfold Inside; decide,z⟩
  · exact ⟨2,1,by unfold Inside; decide,z⟩

theorem splits_box (a b : ℕ) (s : Bool) (ha : 0<a) (hb : 0<b) : Splits (box a b s) := by
  by_cases aBig : 3≤a
  · have low := splits_box (a-2) b s (by omega) hb
    have hh := splits_add (box_valid s (show 0<a-2 by omega) hb) low S200
    rwa [←box_add_left, Nat.sub_add_cancel (show 2≤a by omega)] at hh
  by_cases bBig : 3≤b
  · have low := splits_box a (b-2) s ha (by omega)
    have hh := splits_add (box_valid s ha (show 0<b-2 by omega)) low S020
    rwa [←box_add_right, Nat.sub_add_cancel (show 2≤b by omega)] at hh
  have aa : a=1 ∨ a=2 := by omega
  have bb : b=1 ∨ b=2 := by omega
  rcases aa with rfl | rfl <;> rcases bb with rfl | rfl <;> cases s <;>
    first | exact S110 | exact S111 | exact S120 | exact S121 |
            exact S210 | exact S211 | exact S220 | exact S221
termination_by a+b
decreasing_by all_goals omega

open Finset

def total {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) : Data :=
  ⟨∑ i, (a i : ℤ), ∑ i, (b i : ℤ), ∑ i,bit 0 (s i),
   ∑ i,bit (a i) (s i), ∑ i,bit (b i) (s i), ∑ i,bit (a i+b i) (s i)⟩

def zero : Data := ⟨0,0,0,0,0,0⟩

theorem total_zero (a b : Fin 0 → ℕ) (s : Fin 0 → Bool) : total a b s = zero := by
  simp [total,zero]

theorem total_succ {m : ℕ} (a b : Fin (m+1) → ℕ) (s : Fin (m+1) → Bool) :
    total a b s = add (total (fun i => a i.succ) (fun i => b i.succ) (fun i => s i.succ))
      (box (a 0) (b 0) (s 0)) := by
  simp [total,add,box,Fin.sum_univ_succ,Int.add_comm]

theorem zero_valid : Valid zero := by unfold Valid zero; decide
theorem zero_inside : Inside zero 0 0 := by unfold Inside zero; decide
theorem inside_zero {u v : ℤ} (h : Inside zero u v) : u=0 ∧ v=0 := by
  rcases h with ⟨hu,hU,hv,hV,_⟩
  change u≤0 at hU
  change v≤0 at hV
  omega

theorem total_valid {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool)
    (pos : ∀ i, 0<a i ∧ 0<b i) : Valid (total a b s) := by
  induction m with
  | zero => rw [total_zero]; exact zero_valid
  | succ m ih =>
    rw [total_succ]
    exact add_valid _ _ (ih _ _ _ (fun i => pos i.succ)) (box_valid _ (pos 0).1 (pos 0).2)

theorem total_pos {m : ℕ} (hm : 0 < m) (a b : Fin m → ℕ) (s : Fin m → Bool)
    (pos : ∀ i,0<a i ∧ 0<b i) : 0 < (total a b s).1 ∧ 0 < (total a b s).2.1 := by
  have one : Fin m := ⟨0,hm⟩
  have key (c : Fin m → ℕ) (hc : 0<c one) : (0:ℤ) < ∑ i,(c i : ℤ) := by
    have hh := Finset.single_le_sum (f := fun i : Fin m => (c i : ℤ)) (fun i _ => by positivity) (Finset.mem_univ one)
    omega
  exact ⟨key a (pos one).1,key b (pos one).2⟩

theorem inside_box {a b x y : ℕ} (s : Bool) :
  Inside (box a b s) x y ↔ x≤a ∧ y≤b ∧ (x+y)%2=s.toNat := by
  cases s <;> simp only [Inside,box,bit,Bool.toNat_false,Bool.toNat_true,Nat.zero_add,Nat.add_zero]
  all_goals push_cast
  all_goals omega

open Finset

theorem after_total {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool)
    (pos : ∀ i, 0 < a i ∧ 0 < b i) {h : Data} (sh : Splits h)
    (u v : ℤ) (hit : Inside (add (total a b s) h) u v) :
    ∃ x y, Inside h x y ∧ Inside (total a b s) (u-x) (v-y) := by
  by_cases hm : 0 < m
  · have hp := total_pos hm a b s pos
    exact sh _ (total_valid a b s pos) hp.1 hp.2 _ _ hit
  · have em : m=0 := by omega
    subst m
    rw [total_zero] at hit ⊢
    have id : add zero h=h := by cases h; simp [add,zero]
    rw [id] at hit
    exact ⟨u,v,hit,by simpa using zero_inside⟩

theorem aggregate (split : ∀ a b s, 0 < a → 0 < b → Splits (box a b s))
    {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool)
    (pos : ∀ i,0 < a i ∧ 0 < b i) (u v : ℤ) :
    Inside (total a b s) u v ↔
    ∃ x y : Fin m → ℤ, (∀ i,Inside (box (a i) (b i) (s i)) (x i) (y i)) ∧
      ∑ i,x i = u ∧ ∑ i,y i = v := by
  induction m generalizing u v with
  | zero =>
    rw [total_zero]
    constructor
    · intro h
      obtain ⟨rfl,rfl⟩ := inside_zero h
      exact ⟨Fin.elim0,Fin.elim0,fun i => i.elim0,by simp,by simp⟩
    · rintro ⟨x,y,_,rfl,rfl⟩
      simpa using zero_inside
  | succ m ih =>
    rw [total_succ]
    constructor
    · intro hit
      obtain ⟨w,z,h0,rest⟩ := after_total _ _ _ (fun i : Fin m => pos i.succ)
        (split _ _ _ (pos 0).1 (pos 0).2) _ _ hit
      obtain ⟨x,y,ok,sx,sy⟩ := (ih _ _ _ (fun i : Fin m => pos i.succ) _ _).mp rest
      refine ⟨Fin.cons w x,Fin.cons z y,?_,?_,?_⟩
      · exact Fin.cases h0 (fun i => ok i)
      · rw [Fin.sum_univ_succ]; simpa using (show w+(∑ i,x i)=u by omega)
      · rw [Fin.sum_univ_succ]; simpa using (show z+(∑ i,y i)=v by omega)
    · rintro ⟨x,y,ok,rfl,rfl⟩
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ (f := y)]
      have ht := (ih _ _ _ (fun i : Fin m => pos i.succ) _ _).mpr
        ⟨fun i => x i.succ,fun i => y i.succ,fun i => ok i.succ,rfl,rfl⟩
      simpa only [Int.add_comm] using inside_add ht (ok 0)

theorem allocations (split : ∀ a b s, 0 < a → 0 < b → Splits (box a b s))
    {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (pos : ∀ i,0 < a i ∧ 0 < b i) (u v : ℕ) :
    (∃ x y : Fin m → ℕ,
      (∀ i, x i ≤ a i ∧ y i ≤ b i ∧ (x i+y i)%2=(s i).toNat) ∧
      (∑ i,x i)=u ∧ (∑ i,y i)=v) ↔ Inside (total a b s) u v := by
  rw [aggregate split a b s pos]
  constructor
  · rintro ⟨x,y,h,rfl,rfl⟩
    exact ⟨fun i => x i,fun i => y i,fun i => (inside_box _).mpr (h i),by simp,by simp⟩
  · rintro ⟨x,y,h,hx,hy⟩
    have xeq (i) : ((x i).toNat : ℤ)=x i := Int.toNat_of_nonneg (h i).1
    have yeq (i) : ((y i).toNat : ℤ)=y i := Int.toNat_of_nonneg (h i).2.2.1
    refine ⟨fun i => (x i).toNat,fun i => (y i).toNat,fun i => (inside_box _).mp (by
      simpa only [xeq,yeq] using h i),?_,?_⟩
    · exact_mod_cast (show (↑(∑ i,(x i).toNat) : ℤ) = ↑u by simpa only [Nat.cast_sum,xeq] using hx)
    · exact_mod_cast (show (↑(∑ i,(y i).toNat) : ℤ) = ↑v by simpa only [Nat.cast_sum,yeq] using hy)

open Finset

def defect {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (r t : Bool) : ℕ :=
  (univ.filter fun i : Fin m => ((if r then a i else 0)+(if t then b i else 0))%2 ≠ (s i).toNat).card

theorem bit_indicator (n : ℕ) (s : Bool) : bit n s = if n%2 ≠ s.toNat then (1:ℤ) else 0 := by
  cases s <;> simp only [bit,Bool.toNat_false,Bool.toNat_true] <;> split <;> omega

theorem bits_count {m : ℕ} (n : Fin m → ℕ) (s : Fin m → Bool) :
    ∑ i,bit (n i) (s i) = ((univ.filter fun i => n i%2 ≠ (s i).toNat).card : ℤ) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [bit_indicator]
  split <;> rfl

theorem total_corners {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) :
  (total a b s).2.2.1 = ↑(defect a b s false false) ∧
  (total a b s).2.2.2.1 = ↑(defect a b s true false) ∧
  (total a b s).2.2.2.2.1 = ↑(defect a b s false true) ∧
  (total a b s).2.2.2.2.2 = ↑(defect a b s true true) := by
  unfold total defect
  simp only [Bool.false_eq_true,↓reduceIte,add_zero,zero_add]
  exact ⟨bits_count (fun _ => 0) s,bits_count a s,bits_count b s,bits_count (fun i => a i+b i) s⟩

theorem corner_parity {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) :
  defect a b s false false = ∑ i, (s i).toNat := by
  apply Nat.cast_injective (R := ℤ)
  rw [←(total_corners a b s).1,Nat.cast_sum]
  change (∑ i,bit 0 (s i)) = _
  apply sum_congr rfl
  intro i _
  cases s i <;> decide

theorem criterion {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (u v : ℕ) :
  Inside (total a b s) u v ↔
    u ≤ ∑ i,a i ∧ v ≤ ∑ i,b i ∧ (u+v)%2=(∑ i,(s i).toNat)%2 ∧
    ∀ r t : Bool, defect a b s r t ≤ (if r then (∑ i,a i)-u else u) + (if t then (∑ i,b i)-v else v) := by
  let A := ∑ i,a i
  let B := ∑ i,b i
  change Inside (total a b s) u v ↔ u≤A ∧ v≤B ∧ _ ∧ ∀ r t : Bool,defect a b s r t ≤ (if r then A-u else u)+(if t then B-v else v)
  have hA : (total a b s).1 = (A:ℤ) := by simp [total,A]
  have hB : (total a b s).2.1 = (B:ℤ) := by simp [total,B]
  obtain ⟨hd,he,hf,hg⟩ := total_corners a b s
  have parity := corner_parity a b s
  unfold Inside
  rw [hA,hB,hd,he,hf,hg]
  constructor
  · rintro ⟨hu,hU,hv,hV,hpar,h1,h2,h3,h4⟩
    refine ⟨by omega,by omega,by omega,?_⟩
    intro r t
    cases r <;> cases t <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  · rintro ⟨hU,hV,hpar,h⟩
    have h1 := h false false
    have h2 := h true false
    have h3 := h false true
    have h4 := h true true
    simp only [Bool.false_eq_true,↓reduceIte] at h1 h2 h3 h4
    omega

end PEqualNP.Outside.L_lib_846_aux

theorem PEqualNP.Outside.L_lib_846 : ∀ (m : ℕ) (a b : Fin m → ℕ) (s : Fin m → Bool),
  (∀ i, 0 < a i ∧ 0 < b i) →
  let A := ∑ i : Fin m, a i
  let B := ∑ i : Fin m, b i
  let defect := fun (right top : Bool) =>
    (Finset.univ.filter (fun i : Fin m =>
      ((if right then a i else 0) + (if top then b i else 0)) % 2 ≠ (s i).toNat)).card
  ∀ u v : ℕ,
    (∃ x y : Fin m → ℕ,
      (∀ i, x i ≤ a i ∧ y i ≤ b i ∧ (x i + y i) % 2 = (s i).toNat) ∧
      (∑ i : Fin m, x i) = u ∧ (∑ i : Fin m, y i) = v) ↔
    u ≤ A ∧ v ≤ B ∧ (u+v)%2 = (∑ i : Fin m, (s i).toNat)%2 ∧
    ∀ right top : Bool, defect right top ≤
      (if right then A-u else u) + (if top then B-v else v) := by
  intro m a b s pos
  dsimp only
  intro u v
  exact (PEqualNP.Outside.L_lib_846_aux.allocations PEqualNP.Outside.L_lib_846_aux.splits_box a b s pos u v).trans (PEqualNP.Outside.L_lib_846_aux.criterion a b s u v)

import FormulaMass
namespace InverterBridge
open Finset
abbrev Pair := Bool × Bool
def choose (k : Fin 4) (v : Pair) := if k=0 then false else if k=1 then true else if k=2 then v.1 else v.2

theorem two_bits : ∀ Z O : Finset Pair,
    (∀ z ∈ Z, ∀ o ∈ O, ¬ z ≤ o ∧ ¬ o ≤ z) →
    ∃ k : Fin 4, (∀ z ∈ Z,choose k z=false) ∧ (∀ o ∈ O,choose k o=true) := by
  intro Z O h
  have aux : ∀ z o : Fin 16,
      (∀ x : Pair, (z.val.testBit (x.1.toNat*2+x.2.toNat))=true → ∀ y : Pair, (o.val.testBit (y.1.toNat*2+y.2.toNat))=true → ¬ x≤y ∧ ¬ y≤x) →
      ∃ k : Fin 4, (∀ x : Pair,(z.val.testBit (x.1.toNat*2+x.2.toNat))=true → choose k x=false) ∧
        (∀ y : Pair,(o.val.testBit (y.1.toNat*2+y.2.toNat))=true → choose k y=true) := by decide +kernel
  let enc (S : Finset Pair) : Fin 16 := ⟨(decide ((false,false)∈S)).toNat + 2*(decide ((false,true)∈S)).toNat + 4*(decide ((true,false)∈S)).toNat + 8*(decide ((true,true)∈S)).toNat, by grind [Bool.toNat]⟩
  have code (S : Finset Pair) (x : Pair) : ((enc S).val.testBit (x.1.toNat*2+x.2.toNat))=true ↔ x∈S := by
    rcases x with ⟨a,b⟩; cases a <;> cases b <;> simp only [enc] <;> by_cases h1 : (false,false)∈S <;> by_cases h2 : (false,true)∈S <;> by_cases h3 : (true,false)∈S <;> by_cases h4 : (true,true)∈S <;> simp [*] <;> decide
  obtain ⟨k,hz,ho⟩ := aux (enc Z) (enc O) (fun x hx y hy => h x ((code Z x).mp hx) y ((code O y).mp hy))
  exact ⟨k,fun x hx => hz x ((code Z x).mpr hx),fun y hy => ho y ((code O y).mpr hy)⟩

variable {I : Type} [Fintype I] [DecidableEq I]
abbrev X (I : Type) := I → Bool

def lift (P Q : Finset I) (x : X I) (i : I) := if i∈P ∧ i∉Q then true else x i
def anchor (P Q : Finset I) (x : X I) (i : I) := if i∈P then (if i∈Q then x i else true) else false

def Depends (f : X I → Bool) (P : Finset I) :=
  ∀ x y, (∀ i∈P,x i=y i) → f x=f y

theorem anchors {P Q : Finset I} {A B : X I → Bool} (am : Monotone A) (bm : Monotone B)
    (ad : Depends A P) (bd : Depends B Q) {x : X I} (a : A x=true) (b : B x=false) :
    x ≤ lift P Q x ∧ anchor P Q x ≤ lift P Q x ∧
    A (lift P Q x)=true ∧ B (lift P Q x)=false ∧ A (anchor P Q x)=true ∧ B (anchor P Q x)=false := by
  have h1 : x ≤ lift P Q x := by intro i; by_cases h : i∈P ∧ i∉Q <;> simp [lift,h]
  have h2 : anchor P Q x ≤ lift P Q x := by
    intro i; by_cases hp : i∈P <;> by_cases hq : i∈Q <;> simp [anchor,lift,hp,hq]
  have aa : A (lift P Q x)=true := by have h := am h1; rw [a] at h; exact le_antisymm le_top h
  have bb : B (lift P Q x)=false := (bd _ _ (by intro i hi; simp [lift,hi])).trans b
  have ab : A (anchor P Q x)=true := (ad _ _ (by
    intro i hi; by_cases hq : i∈Q <;> simp [anchor,lift,hi,hq])).trans aa
  have ba : B (anchor P Q x)=false := by have h := bm h2; rw [bb] at h; exact le_antisymm h bot_le
  exact ⟨h1,h2,aa,bb,ab,ba⟩

theorem anchor_order {P Q : Finset I} {i j : I} (sub : ∀ t∈P, t∈Q → t=i ∨ t=j)
    {x y : X I} (h : (x i,x j) ≤ (y i,y j)) : anchor P Q x ≤ anchor P Q y := by
  intro t; by_cases hp : t∈P <;> by_cases hq : t∈Q <;> simp [anchor,hp,hq]
  rcases sub t hp hq with rfl|rfl
  · exact h.1
  · exact h.2

theorem replace_two {P Q : Finset I} {A B F G : X I → Bool}
    (am : Monotone A) (bm : Monotone B) (fm : Monotone F) (gm : Antitone G)
    (ad : Depends A P) (bd : Depends B Q) (hg : ∀ x,A x=true → B x=false → F x=G x)
    (i j : I) (sub : ∀ t∈P, t∈Q → t=i ∨ t=j) :
    ∃ k : Fin 4, ∀ x,A x=true → B x=false → F x=choose k (x i,x j) := by
  classical
  let code (x : X I) : Pair := (x i,x j)
  let bucket (v : Bool) := (univ.filter fun x : X I => A x=true ∧ B x=false ∧ F x=v).image code
  have same {x y : X I} (xy : x≤y) (ax : A x=true) (bx : B x=false) (ay : A y=true) (byy : B y=false) :
      F x=F y := le_antisymm (fm xy) (by simpa only [hg x ax bx,hg y ay byy] using gm xy)
  have norm (x : X I) (ax : A x=true) (bx : B x=false) : F x=F (anchor P Q x) := by
    obtain ⟨h1,h2,a1,b1,a2,b2⟩ := anchors am bm ad bd ax bx
    exact (same h1 ax bx a1 b1).trans (same h2 a2 b2 a1 b1).symm
  have cmp {x y : X I} (ax : A x=true) (bx : B x=false) (ay : A y=true) (byy : B y=false)
      (xy : code x ≤ code y) : F x=F y := by
    obtain ⟨_,_,_,_,a1,b1⟩ := anchors am bm ad bd ax bx
    obtain ⟨_,_,_,_,a2,b2⟩ := anchors am bm ad bd ay byy
    exact (norm x ax bx).trans ((same (anchor_order sub xy) a1 b1 a2 b2).trans (norm y ay byy).symm)
  obtain ⟨k,h0,h1⟩ := two_bits (bucket false) (bucket true) (by
    intro z hz o ho
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp ho
    obtain ⟨ax,bx,vx⟩ := (mem_filter.mp hx).2
    obtain ⟨ay,byy,vy⟩ := (mem_filter.mp hy).2
    constructor
    · intro h; have eq := cmp ax bx ay byy h; simp [vx,vy] at eq
    · intro h; have eq := cmp ay byy ax bx h; simp [vx,vy] at eq)
  refine ⟨k,fun x ax bx => ?_⟩
  have inc : code x ∈ bucket (F x) := mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,ax,bx,rfl⟩,rfl⟩
  cases f : F x with
  | false => rw [f] at inc; exact (h0 _ inc).symm
  | true => rw [f] at inc; exact (h1 _ inc).symm
end InverterBridge

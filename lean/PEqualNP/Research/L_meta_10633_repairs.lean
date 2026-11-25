import PEqualNP.Research.L_meta_10633_graph
import PEqualNP.Research.L_meta_10633_universal

namespace PEqualNP.Research.DenseRepairs
open PEqualNP.Research.UniversalInverterRepair

abbrev Mask := BitVec 7
inductive Tree where
  | input (i : Fin 7)
  | lit (b : Bool)
  | meet (a b : Tree)
  | join (a b : Tree)
  deriving Repr

def Tree.size : Tree → Nat
  | .input _ => 0
  | .lit _ => 1
  | .meet a b | .join a b => 1 + a.size + b.size

def Tree.eval : Tree → Mask → Bool
  | .input i, x => x.getLsbD i.val
  | .lit b, _ => b
  | .meet a b, x => a.eval x && b.eval x
  | .join a b, x => a.eval x || b.eval x

def edgeMasks : List Mask := [9, 10, 17, 20, 33, 34, 40, 48, 66, 68, 72, 80, 96]
def graph (x : Mask) := edgeMasks.any (fun e => (x &&& e) == e)
def signal (join : Bool) (s x : Mask) := if join then (x &&& s) != 0 else (x &&& s) == s
def budget (s : Mask) := ((List.finRange 7).filter (fun i => s.getLsbD i.val)).length

theorem posted : ∀ x : Mask, graph x = DenseSeven.target (fun i => x.getLsbD i.val) := by
  decide +kernel

/-- Row order is inclusion of selected vertices. -/
def rawRow (x : Mask) : Finset (Fin 7) := Finset.univ.filter (fun i => x.getLsbD i.val)
def maskOf (x : Finset (Fin 7)) : Mask := (List.finRange 7).foldl (fun m i => if i ∈ x then m ||| ((1 : Mask) <<< i.val) else m) 0

theorem mask_roundtrip : ∀ x : Mask, maskOf (rawRow x) = x := by decide +kernel

private def t0 : Tree := (.join (.input 3) (.join (.input 4) (.join (.input 5) (.input 6))))
private def t1 : Tree := (.lit true)
private def t2 : Tree := (.meet (.join (.input 4) (.meet (.input 5) (.input 6))) (.join (.input 5) (.input 6)))
private def t3 : Tree := (.join (.input 5) (.meet (.input 6) (.join (.input 2) (.input 3))))
private def t4 : Tree := (.meet (.join (.input 3) (.meet (.input 5) (.input 6))) (.join (.input 5) (.input 6)))
private def t5 : Tree := (.join (.input 5) (.input 6))
private def t6 : Tree := (.join (.input 5) (.meet (.input 6) (.join (.input 1) (.input 2))))
private def t7 : Tree := (.meet (.input 6) (.join (.input 2) (.input 5)))
private def t8 : Tree := (.join (.input 6) (.meet (.input 5) (.join (.input 0) (.input 1))))
private def t9 : Tree := (.meet (.join (.input 1) (.meet (.input 5) (.input 6))) (.join (.input 5) (.input 6)))
private def t10 : Tree := (.meet (.input 5) (.join (.input 0) (.input 6)))
private def t11 : Tree := (.meet (.input 5) (.input 6))
private def t12 : Tree := (.meet (.join (.input 0) (.input 6)) (.join (.input 3) (.input 4)))
private def t13 : Tree := (.meet (.input 6) (.join (.input 3) (.input 4)))
private def t14 : Tree := (.join (.input 6) (.meet (.input 4) (.join (.input 0) (.input 2))))
private def t15 : Tree := (.meet (.join (.input 4) (.meet (.input 2) (.input 6))) (.join (.input 2) (.input 6)))
private def t16 : Tree := (.join (.input 6) (.meet (.input 0) (.input 4)))
private def t17 : Tree := (.meet (.input 6) (.join (.input 1) (.input 4)))
private def t18 : Tree := (.meet (.input 4) (.join (.input 0) (.input 6)))
private def t19 : Tree := (.meet (.input 4) (.input 6))
private def t20 : Tree := (.join (.input 6) (.meet (.input 0) (.input 3)))
private def t21 : Tree := (.meet (.input 6) (.join (.input 2) (.input 3)))
private def t22 : Tree := (.join (.input 6) (.meet (.input 3) (.join (.input 0) (.input 1))))
private def t23 : Tree := (.meet (.join (.input 1) (.meet (.input 3) (.input 6))) (.join (.input 3) (.input 6)))
private def t24 : Tree := (.meet (.input 3) (.join (.input 0) (.input 6)))
private def t25 : Tree := (.meet (.input 3) (.input 6))
private def t26 : Tree := (.input 6)
private def t27 : Tree := (.meet (.input 6) (.join (.input 1) (.input 2)))
private def t28 : Tree := (.meet (.input 2) (.input 6))
private def t29 : Tree := (.meet (.input 1) (.input 6))
private def t30 : Tree := (.lit false)
private def t31 : Tree := (.join (.input 3) (.join (.input 4) (.input 5)))
private def t32 : Tree := (.join (.input 5) (.meet (.input 2) (.input 4)))
private def t33 : Tree := (.meet (.input 5) (.join (.input 3) (.input 4)))
private def t34 : Tree := (.join (.input 5) (.meet (.input 4) (.join (.input 0) (.input 2))))
private def t35 : Tree := (.meet (.input 4) (.join (.input 2) (.input 5)))
private def t36 : Tree := (.meet (.input 5) (.join (.input 1) (.input 4)))
private def t37 : Tree := (.meet (.join (.input 4) (.meet (.input 0) (.input 5))) (.join (.input 0) (.input 5)))
private def t38 : Tree := (.meet (.input 4) (.input 5))
private def t39 : Tree := (.join (.input 5) (.meet (.input 1) (.input 3)))
private def t40 : Tree := (.join (.input 5) (.meet (.input 0) (.input 3)))
private def t41 : Tree := (.input 5)
private def t42 : Tree := (.meet (.join (.input 1) (.meet (.input 3) (.input 5))) (.join (.input 3) (.input 5)))
private def t43 : Tree := (.meet (.join (.input 3) (.meet (.input 0) (.input 5))) (.join (.input 0) (.input 5)))
private def t44 : Tree := (.meet (.input 3) (.input 5))
private def t45 : Tree := (.meet (.input 5) (.join (.input 0) (.input 1)))
private def t46 : Tree := (.meet (.input 1) (.input 5))
private def t47 : Tree := (.meet (.input 0) (.input 5))
private def t48 : Tree := (.join (.input 3) (.input 4))
private def t49 : Tree := (.meet (.join (.input 3) (.input 4)) (.join (.input 0) (.input 2)))
private def t50 : Tree := (.meet (.input 2) (.input 4))
private def t51 : Tree := (.meet (.join (.input 3) (.input 4)) (.join (.input 0) (.input 1)))
private def t52 : Tree := (.meet (.input 1) (.input 3))
private def t53 : Tree := (.meet (.input 0) (.join (.input 3) (.input 4)))
private def t54 : Tree := (.meet (.input 4) (.join (.input 0) (.input 2)))
private def t55 : Tree := (.meet (.input 0) (.input 4))
private def t56 : Tree := (.meet (.input 3) (.join (.input 0) (.input 1)))
private def t57 : Tree := (.meet (.input 0) (.input 3))

private def andRepairs : Array (Option Tree) :=
  #[none, none, none, none, none, none, none, some t0, none, some t1, some t1, some t1, none, some t1, some t1, some t1, none, some t1, none, some t1, some t1, some t1, some t1, some t1, none, some t1, some t1, some t1, some t1, some t1, some t1, some t1, none, some t1, some t1, some t1, none, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, none, none, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1, some t1]
private def orRepairs : Array (Option Tree) :=
  #[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some t2, none, none, none, some t3, none, none, none, some t4, some t5, some t6, some t5, some t7, some t8, some t9, some t10, some t11, none, none, none, none, none, none, some t12, some t13, none, none, some t14, some t15, some t16, some t17, some t18, some t19, none, none, some t20, some t21, some t22, some t23, some t24, some t25, some t26, some t27, some t26, some t28, some t26, some t29, some t30, some t30, none, some t31, none, some t32, none, none, none, some t33, none, some t32, some t34, some t35, none, some t36, some t37, some t38, none, some t39, some t40, some t41, none, some t42, some t43, some t44, some t41, some t41, some t41, some t30, some t45, some t46, some t47, some t30, some t48, some t48, some t49, some t50, some t51, some t52, some t53, some t30, some t54, some t50, some t54, some t50, some t55, some t30, some t55, some t30, some t56, some t52, some t57, some t30, some t56, some t52, some t57, some t30, some t30, some t30, some t30, some t30, some t30, some t30, some t30, some t30]

def repair (join : Bool) (s : Mask) : Option Tree :=
  ((if join then orRepairs else andRepairs)[s.toNat]?).join

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checked : ∀ j s, ((repair j s).map (fun t => decide (t.size ≤ budget s) &&
    (List.finRange 128).all (fun a =>
      let x := BitVec.ofNat 7 a.val
      if graph x then signal j s x || t.eval x else !(signal j s x && t.eval x)))).getD true = true := by
  decide +kernel

theorem repair_size {j s t} (h : repair j s = some t) : t.size ≤ budget s := by
  have ok := checked j s
  simp only [h,Option.map_some,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact ok.1

theorem repair_fits {j s t} (h : repair j s = some t) :
    Fits (fun x : Finset (Fin 7) => graph (maskOf x)) (fun x => signal j s (maskOf x))
      (fun x => t.eval (maskOf x)) := by
  have ok := checked j s
  simp only [h,Option.map_some,Option.getD_some,Bool.and_eq_true,List.all_eq_true] at ok
  have chk (x : Finset (Fin 7)) := ok.2 (⟨(maskOf x).toNat,(maskOf x).isLt⟩ : Fin 128) (by simp)
  simp only [BitVec.ofNat_toNat] at chk
  constructor <;> intro x fx dx <;> simpa [fx,dx] using chk x

theorem every_suffix {j s t} (h : repair j s = some t) :
    Safe (fun x : Finset (Fin 7) => graph (maskOf x)) (fun x => signal j s (maskOf x))
      (fun x => t.eval (maskOf x)) := safe_of_fits (repair_fits h)

def countAt (j : Bool) (k : Nat) := ((List.finRange 128).filter (fun i =>
  let s := BitVec.ofNat 7 i.val
  budget s == k && (repair j s).isSome)).length

theorem counts : (List.range 8).map (countAt false) = [0,0,13,35,35,21,7,1] ∧
    (List.range 8).map (countAt true) = [0,0,3,21,35,21,7,1] := by decide +kernel

end PEqualNP.Research.DenseRepairs

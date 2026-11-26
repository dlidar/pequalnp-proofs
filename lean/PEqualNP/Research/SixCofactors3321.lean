import PEqualNP.Research.GateCuts3321

namespace PEqualNP.Research.SixCofactors3321
open PEqualNP.Research.GateCuts3321

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

def graph862 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5)

def graph862_0 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5)

theorem lower_graph862_0 : Lower graph862_0 8 := contains_six _ ![0,4,2,0,3,1,5,0] (by decide +kernel)

private theorem at_graph862_0 : cut graph862 7 false = graph862_0 := funext (by decide +kernel)

theorem lower_graph862 : Lower graph862 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph862 7 from ⟨![true,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,true,false,false,true,false,false,false], by decide⟩
    (at_graph862_0 ▸ lower_graph862_0)

def graph4958 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5) || (x 3 && x 4)

private theorem at_graph4958_0 : cut graph4958 3 false = graph862 := funext (by decide +kernel)

theorem lower_graph4958 : Lower graph4958 10 := by
  exact one_step (k:=9) (b:=false) (by decide)
    (show Dep graph4958 3 from ⟨![false,false,false,false,true,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,true,false,false,true,false,false,false], by decide⟩
    (at_graph4958_0 ▸ lower_graph862)

def graph4973 : Fn 8 := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5) || (x 3 && x 4)

def graph4973_0 : Fn 8 := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5)

def graph4973_0_0 : Fn 8 := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5)

theorem lower_graph4973_0_0 : Lower graph4973_0_0 8 := contains_six _ ![0,4,2,0,1,3,5,0] (by decide +kernel)

private theorem at_graph4973_0_0 : cut graph4973_0 7 false = graph4973_0_0 := funext (by decide +kernel)

theorem lower_graph4973_0 : Lower graph4973_0 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph4973_0 7 from ⟨![true,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![true,false,false,false,true,false,false,false], by decide⟩
    (at_graph4973_0_0 ▸ lower_graph4973_0_0)

private theorem at_graph4973_0 : cut graph4973 3 false = graph4973_0 := funext (by decide +kernel)

theorem lower_graph4973 : Lower graph4973 10 := by
  exact one_step (k:=9) (b:=false) (by decide)
    (show Dep graph4973 3 from ⟨![false,false,false,false,true,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![true,false,false,false,true,false,false,false], by decide⟩
    (at_graph4973_0 ▸ lower_graph4973_0)

def graph5804 : Fn 8 := fun x => (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 4)

def graph5804_1 : Fn 8 := fun x => (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 3)

def graph5804_1_0 : Fn 8 := fun x => (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6)

theorem lower_graph5804_1_0 : Lower graph5804_1_0 8 := contains_six _ ![0,4,2,0,0,3,1,5] (by decide +kernel)

private theorem at_graph5804_1_0 : cut graph5804_1 3 false = graph5804_1_0 := funext (by decide +kernel)

theorem lower_graph5804_1 : Lower graph5804_1 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph5804_1 3 from ⟨![false,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,true,false,false,false,true,false,false], by decide⟩
    (at_graph5804_1_0 ▸ lower_graph5804_1_0)

private theorem at_graph5804_1 : cut graph5804 4 true = graph5804_1 := funext (by decide +kernel)

theorem lower_graph5804 : Lower graph5804 10 := by
  exact one_step (k:=9) (b:=true) (by decide)
    (show Dep graph5804 4 from ⟨![false,false,false,true,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,false,false,true,false,false,false,false], by decide⟩
    (at_graph5804_1 ▸ lower_graph5804_1)

def graph5805 : Fn 8 := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 4)

def graph5805_0 : Fn 8 := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6)

private theorem at_graph5805_0_0 : cut graph5805_0 4 false = graph5804_1_0 := funext (by decide +kernel)

theorem lower_graph5805_0 : Lower graph5805_0 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph5805_0 4 from ⟨![true,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,true,false,false,false,true,false,false], by decide⟩
    (at_graph5805_0_0 ▸ lower_graph5804_1_0)

private theorem at_graph5805_0 : cut graph5805 3 false = graph5805_0 := funext (by decide +kernel)

def graph5805_1 : Fn 8 := fun x => (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 4)

private theorem at_graph5805_1_0 : cut graph5805_1 4 false = graph5804_1_0 := funext (by decide +kernel)

theorem lower_graph5805_1 : Lower graph5805_1 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph5805_1 4 from ⟨![false,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,true,false,false,false,true,false,false], by decide⟩
    (at_graph5805_1_0 ▸ lower_graph5804_1_0)

private theorem at_graph5805_1 : cut graph5805 3 true = graph5805_1 := funext (by decide +kernel)

theorem lower_graph5805 : Lower graph5805 11 := by
  apply two_steps (k:=9) (show Dep graph5805 3 from ⟨![false,false,false,false,true,false,false,false],by decide⟩)
  · intro b;cases b
    · exact ⟨![false,false,false,false,false,false,false,false], ![true,false,false,false,true,false,false,false], by decide⟩
    · exact ⟨![false,false,false,false,false,false,false,false], ![false,false,false,false,true,false,false,false], by decide⟩
  · intro b;cases b
    · exact at_graph5805_0 ▸ lower_graph5805_0
    · exact at_graph5805_1 ▸ lower_graph5805_1

def graph13726 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 5)

def graph13726_0 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 2 && x 4) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 5)

def graph13726_0_0 : Fn 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 2 && x 4) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 5)

theorem lower_graph13726_0_0 : Lower graph13726_0_0 8 := contains_six _ ![0,0,4,2,3,1,5,0] (by decide +kernel)

private theorem at_graph13726_0_0 : cut graph13726_0 7 false = graph13726_0_0 := funext (by decide +kernel)

theorem lower_graph13726_0 : Lower graph13726_0 9 := by
  exact one_step (k:=8) (b:=false) (by decide)
    (show Dep graph13726_0 7 from ⟨![true,false,false,false,false,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,false,true,false,true,false,false,false], by decide⟩
    (at_graph13726_0_0 ▸ lower_graph13726_0_0)

private theorem at_graph13726_0 : cut graph13726 1 false = graph13726_0 := funext (by decide +kernel)

theorem lower_graph13726 : Lower graph13726 10 := by
  exact one_step (k:=9) (b:=false) (by decide)
    (show Dep graph13726 1 from ⟨![false,false,false,false,true,false,false,false],by decide⟩)
    ⟨![false,false,false,false,false,false,false,false], ![false,false,true,false,true,false,false,false], by decide⟩
    (at_graph13726_0 ▸ lower_graph13726_0)

end PEqualNP.Research.SixCofactors3321

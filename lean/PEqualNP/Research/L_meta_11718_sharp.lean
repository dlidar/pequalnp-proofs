import PEqualNP.Research.L_meta_11718_graph
import PEqualNP.Research.L_meta_11718_circuits

namespace PEqualNP.Research.SevenVertexSharp
open PEqualNP.CircuitLowerBounds PEqualNP.Research.SingleInverter
open PEqualNP.Research.SevenVertexInverter PEqualNP.Research.InverterCircuit

def maskRow (m : Fin 128) : Row (Fin 7) := Finset.univ.filter (fun i => m.val.testBit i.val)
def vertices (s : Row (Fin 7)) : List ℕ := ((List.finRange 7).filter (fun i => i ∈ s)).map Fin.val

def accumulate (op : GateOp) (next a : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([],a)
  | b :: tail =>
    let r := accumulate op (next+1) next tail
    (⟨op,[a,b]⟩ :: r.1, r.2)

def block (op : GateOp) (next : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([⟨op,[]⟩],next)
  | a :: tail => accumulate op next a tail

def shift (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (fun i => if i < 7 then i else i+n)⟩

-- A false negative needs a conjunction before the inverter, a false positive a disjunction.
-- If the relevant set is empty the change is already monotone.
def puncture (x : Row (Fin 7)) : Circuit :=
  let p := graph x
  let r := vertices (needed graph x)
  let d := block (if p then .and else .or) 7 r
  let inv := 7 + d.1.length
  let pre := if r.isEmpty then [] else d.1 ++ [⟨.not,[d.2]⟩]
  let afterRef := 7 + pre.length + reference.gates.length
  let other := block (if p then .or else .and) afterRef
    (vertices (if p then Finset.univ \ x else x))
  let last := afterRef + other.1.length
  let mid := if r.isEmpty then [] else [⟨if p then .or else .and,[inv, other.2]⟩]
  let gs := pre ++ reference.gates.map (shift pre.length) ++ other.1 ++ mid ++
    [⟨if p then .and else .or,[reference.output + pre.length, if r.isEmpty then other.2 else last]⟩]
  ⟨gs,last + mid.length⟩

def arityOK (g : Gate) := g.inputs.length ≤ 2
def monoGate (g : Gate) : Bool := match g.op with | .and | .or => true | _ => false
def invGate (g : Gate) : Bool := match g.op with | .not => true | _ => false

def shapeOK (x : Row (Fin 7)) : Bool :=
  let gs := (puncture x).gates
  let k := (needed graph x).card
  gs.all (fun g => decide (g.inputs.length ≤ 2)) &&
    (if k = 0 then gs.all monoGate else
      (gs.take (k-1)).all monoGate && ((gs[k-1]?).any invGate) &&
      (gs.drop k).all monoGate)

theorem maskRow_surj (s : Row (Fin 7)) : ∃ m : Fin 128, maskRow m = s := by
  revert s
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem shape_all : ∀ m : Fin 128, shapeOK (maskRow m) = true := by decide +kernel

def decRow (m : Fin 128) : List Bool := List.ofFn (fun i : Fin 7 => m.val.testBit i.val)

theorem input_mask (m : Fin 128) : input (maskRow m) = decRow m := by
  simp [input,maskRow,decRow]

def agreesExcept (m t : Fin 128) : Bool :=
  (puncture (maskRow m)).eval (decRow t) == (if t = m then !graph (maskRow t) else graph (maskRow t))

set_option maxRecDepth 16000 in
private theorem mask_0 : ∀ t, agreesExcept 0 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_1 : ∀ t, agreesExcept 1 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_2 : ∀ t, agreesExcept 2 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_3 : ∀ t, agreesExcept 3 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_4 : ∀ t, agreesExcept 4 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_5 : ∀ t, agreesExcept 5 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_6 : ∀ t, agreesExcept 6 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_7 : ∀ t, agreesExcept 7 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_8 : ∀ t, agreesExcept 8 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_9 : ∀ t, agreesExcept 9 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_10 : ∀ t, agreesExcept 10 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_11 : ∀ t, agreesExcept 11 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_12 : ∀ t, agreesExcept 12 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_13 : ∀ t, agreesExcept 13 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_14 : ∀ t, agreesExcept 14 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_15 : ∀ t, agreesExcept 15 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_16 : ∀ t, agreesExcept 16 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_17 : ∀ t, agreesExcept 17 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_18 : ∀ t, agreesExcept 18 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_19 : ∀ t, agreesExcept 19 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_20 : ∀ t, agreesExcept 20 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_21 : ∀ t, agreesExcept 21 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_22 : ∀ t, agreesExcept 22 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_23 : ∀ t, agreesExcept 23 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_24 : ∀ t, agreesExcept 24 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_25 : ∀ t, agreesExcept 25 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_26 : ∀ t, agreesExcept 26 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_27 : ∀ t, agreesExcept 27 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_28 : ∀ t, agreesExcept 28 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_29 : ∀ t, agreesExcept 29 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_30 : ∀ t, agreesExcept 30 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_31 : ∀ t, agreesExcept 31 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_32 : ∀ t, agreesExcept 32 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_33 : ∀ t, agreesExcept 33 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_34 : ∀ t, agreesExcept 34 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_35 : ∀ t, agreesExcept 35 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_36 : ∀ t, agreesExcept 36 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_37 : ∀ t, agreesExcept 37 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_38 : ∀ t, agreesExcept 38 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_39 : ∀ t, agreesExcept 39 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_40 : ∀ t, agreesExcept 40 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_41 : ∀ t, agreesExcept 41 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_42 : ∀ t, agreesExcept 42 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_43 : ∀ t, agreesExcept 43 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_44 : ∀ t, agreesExcept 44 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_45 : ∀ t, agreesExcept 45 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_46 : ∀ t, agreesExcept 46 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_47 : ∀ t, agreesExcept 47 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_48 : ∀ t, agreesExcept 48 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_49 : ∀ t, agreesExcept 49 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_50 : ∀ t, agreesExcept 50 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_51 : ∀ t, agreesExcept 51 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_52 : ∀ t, agreesExcept 52 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_53 : ∀ t, agreesExcept 53 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_54 : ∀ t, agreesExcept 54 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_55 : ∀ t, agreesExcept 55 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_56 : ∀ t, agreesExcept 56 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_57 : ∀ t, agreesExcept 57 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_58 : ∀ t, agreesExcept 58 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_59 : ∀ t, agreesExcept 59 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_60 : ∀ t, agreesExcept 60 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_61 : ∀ t, agreesExcept 61 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_62 : ∀ t, agreesExcept 62 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_63 : ∀ t, agreesExcept 63 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_64 : ∀ t, agreesExcept 64 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_65 : ∀ t, agreesExcept 65 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_66 : ∀ t, agreesExcept 66 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_67 : ∀ t, agreesExcept 67 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_68 : ∀ t, agreesExcept 68 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_69 : ∀ t, agreesExcept 69 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_70 : ∀ t, agreesExcept 70 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_71 : ∀ t, agreesExcept 71 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_72 : ∀ t, agreesExcept 72 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_73 : ∀ t, agreesExcept 73 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_74 : ∀ t, agreesExcept 74 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_75 : ∀ t, agreesExcept 75 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_76 : ∀ t, agreesExcept 76 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_77 : ∀ t, agreesExcept 77 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_78 : ∀ t, agreesExcept 78 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_79 : ∀ t, agreesExcept 79 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_80 : ∀ t, agreesExcept 80 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_81 : ∀ t, agreesExcept 81 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_82 : ∀ t, agreesExcept 82 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_83 : ∀ t, agreesExcept 83 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_84 : ∀ t, agreesExcept 84 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_85 : ∀ t, agreesExcept 85 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_86 : ∀ t, agreesExcept 86 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_87 : ∀ t, agreesExcept 87 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_88 : ∀ t, agreesExcept 88 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_89 : ∀ t, agreesExcept 89 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_90 : ∀ t, agreesExcept 90 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_91 : ∀ t, agreesExcept 91 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_92 : ∀ t, agreesExcept 92 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_93 : ∀ t, agreesExcept 93 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_94 : ∀ t, agreesExcept 94 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_95 : ∀ t, agreesExcept 95 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_96 : ∀ t, agreesExcept 96 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_97 : ∀ t, agreesExcept 97 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_98 : ∀ t, agreesExcept 98 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_99 : ∀ t, agreesExcept 99 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_100 : ∀ t, agreesExcept 100 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_101 : ∀ t, agreesExcept 101 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_102 : ∀ t, agreesExcept 102 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_103 : ∀ t, agreesExcept 103 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_104 : ∀ t, agreesExcept 104 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_105 : ∀ t, agreesExcept 105 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_106 : ∀ t, agreesExcept 106 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_107 : ∀ t, agreesExcept 107 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_108 : ∀ t, agreesExcept 108 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_109 : ∀ t, agreesExcept 109 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_110 : ∀ t, agreesExcept 110 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_111 : ∀ t, agreesExcept 111 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_112 : ∀ t, agreesExcept 112 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_113 : ∀ t, agreesExcept 113 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_114 : ∀ t, agreesExcept 114 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_115 : ∀ t, agreesExcept 115 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_116 : ∀ t, agreesExcept 116 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_117 : ∀ t, agreesExcept 117 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_118 : ∀ t, agreesExcept 118 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_119 : ∀ t, agreesExcept 119 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_120 : ∀ t, agreesExcept 120 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_121 : ∀ t, agreesExcept 121 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_122 : ∀ t, agreesExcept 122 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_123 : ∀ t, agreesExcept 123 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_124 : ∀ t, agreesExcept 124 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_125 : ∀ t, agreesExcept 125 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_126 : ∀ t, agreesExcept 126 t = true := by decide +kernel
set_option maxRecDepth 16000 in
private theorem mask_127 : ∀ t, agreesExcept 127 t = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem matrix (m : Fin 128) : ∀ t, agreesExcept m t = true := by
  fin_cases m
  · exact mask_0
  · exact mask_1
  · exact mask_2
  · exact mask_3
  · exact mask_4
  · exact mask_5
  · exact mask_6
  · exact mask_7
  · exact mask_8
  · exact mask_9
  · exact mask_10
  · exact mask_11
  · exact mask_12
  · exact mask_13
  · exact mask_14
  · exact mask_15
  · exact mask_16
  · exact mask_17
  · exact mask_18
  · exact mask_19
  · exact mask_20
  · exact mask_21
  · exact mask_22
  · exact mask_23
  · exact mask_24
  · exact mask_25
  · exact mask_26
  · exact mask_27
  · exact mask_28
  · exact mask_29
  · exact mask_30
  · exact mask_31
  · exact mask_32
  · exact mask_33
  · exact mask_34
  · exact mask_35
  · exact mask_36
  · exact mask_37
  · exact mask_38
  · exact mask_39
  · exact mask_40
  · exact mask_41
  · exact mask_42
  · exact mask_43
  · exact mask_44
  · exact mask_45
  · exact mask_46
  · exact mask_47
  · exact mask_48
  · exact mask_49
  · exact mask_50
  · exact mask_51
  · exact mask_52
  · exact mask_53
  · exact mask_54
  · exact mask_55
  · exact mask_56
  · exact mask_57
  · exact mask_58
  · exact mask_59
  · exact mask_60
  · exact mask_61
  · exact mask_62
  · exact mask_63
  · exact mask_64
  · exact mask_65
  · exact mask_66
  · exact mask_67
  · exact mask_68
  · exact mask_69
  · exact mask_70
  · exact mask_71
  · exact mask_72
  · exact mask_73
  · exact mask_74
  · exact mask_75
  · exact mask_76
  · exact mask_77
  · exact mask_78
  · exact mask_79
  · exact mask_80
  · exact mask_81
  · exact mask_82
  · exact mask_83
  · exact mask_84
  · exact mask_85
  · exact mask_86
  · exact mask_87
  · exact mask_88
  · exact mask_89
  · exact mask_90
  · exact mask_91
  · exact mask_92
  · exact mask_93
  · exact mask_94
  · exact mask_95
  · exact mask_96
  · exact mask_97
  · exact mask_98
  · exact mask_99
  · exact mask_100
  · exact mask_101
  · exact mask_102
  · exact mask_103
  · exact mask_104
  · exact mask_105
  · exact mask_106
  · exact mask_107
  · exact mask_108
  · exact mask_109
  · exact mask_110
  · exact mask_111
  · exact mask_112
  · exact mask_113
  · exact mask_114
  · exact mask_115
  · exact mask_116
  · exact mask_117
  · exact mask_118
  · exact mask_119
  · exact mask_120
  · exact mask_121
  · exact mask_122
  · exact mask_123
  · exact mask_124
  · exact mask_125
  · exact mask_126
  · exact mask_127

theorem maskRow_injective : Function.Injective maskRow :=
  by
  intro m t h
  have htest : ∀ a b : Fin 128, maskRow a = maskRow b → a = b := by decide +kernel
  exact htest m t h

theorem flip_truth (x y : Row (Fin 7)) :
    (puncture x).eval (input y) = if y = x then !graph y else graph y := by
  obtain ⟨m,rfl⟩ := maskRow_surj x
  obtain ⟨t,rfl⟩ := maskRow_surj y
  simpa [agreesExcept,input_mask, maskRow_injective.eq_iff] using matrix m t

theorem flip_shape (x : Row (Fin 7)) : shapeOK x = true := by
  obtain ⟨m,rfl⟩ := maskRow_surj x
  exact shape_all m

end PEqualNP.Research.SevenVertexSharp

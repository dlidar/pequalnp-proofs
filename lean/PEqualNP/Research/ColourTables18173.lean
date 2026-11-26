import PEqualNP.Outside.L_meta_18113
import Mathlib.Combinatorics.SetFamily.LYM

namespace PEqualNP.Research.ColourProfiles18173

open PEqualNP.Outside.L_meta_18113

abbrev Core := Fin 1024
abbrev Neighbours := Fin 32
abbrev Row := BitVec 32
abbrev Label := Fin 83

def input (c : Core) (z : Neighbours) (j : Fin 15) : Bool :=
  (32*c.val + z.val).testBit j.val

def posted := fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))


theorem posted_eq : posted = targetFun := rfl

def packed : BitVec 32768 := 0x1ffffff0357ffff0357ffff0357ffff03ffffff03ff57ff03ff57ff03ff57ff03ffffff03ffffff03ffffff03ffffff03ffffff00000000000000000537ffff0537ffff000000000f1fffff0537ffff0f3fffff0f3f5f7f0f3f5f7f0f3fffff0f3fffff0f3f5f7f0f3fffff0f3fffff0f3fffff00000000000000000537ffff05ffffff0357ffff0f5fffff0777ffff0fffffff0fff5fff0fff5fff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff000000000000000005ff37ff05ff37ff0f5f3f7f0f5f3f7f0fff3fff0fff3fff000000000fff1fff05ff37ff0fff3fff0f5f3f7f0fff3fff0fff3fff0fff3fff000000000000000005ff37ff05ffffff0f5fffff0f5fffff0fffffff0fffffff03ff57ff0fff5fff07ff77ff0fffffff0fffffff0fffffff0fffffff0fffffff000000000000000005ffffff05ffffff0f5f3f7f0f5fffff0fffffff0fffffff0f3f5f7f0fff5fff0fffffff0fffffff0f7f7f7f0fffffff0fffffff0fffffff000000000000000005ffffff05ffffff0f5fffff0f5fffff0fffffff0fffffff0fff5fff0fff5fff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff00000000111fffff00000000111fffff00000000111fffff3337ffff333fffff333f777f333fffff333f777f333fffff333f777f333fffff333fffff333fffff00000000111fffff0000000011ffffff0357ffff135fffff3377ffff33ffffff33ff77ff33ffffff33ff77ff33ffffff33ffffff33ffffff33ffffff33ffffff00000000111fffff0537ffff153fffff000000001f1fffff3737ffff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff5557ffff555fffff5577ffff55ffffff5757ffff5f5fffff7777ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555f777f555fffff55ff77ff55ffffff5f5f7f7f5f5fffffffffffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff555f777f555fffff55ff77ff55ffffff5f5fffff5f5fffffffffffffffffffff77ff77ffffffffff77ff77ffffffffff7fffffffffffffffffffffffffffffff555f777f555fffff55ffffff55ffffff5f5f7f7f5f5fffffffffffffffffffff7f7f7f7fffffffff7fffffffffffffff7f7f7f7fffffffffffffffffffffffff555fffff555fffff55ffffff55ffffff5f5fffff5f5fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000011ff1fff0000000011ff1fff33773f7f33ff3fff33773f7f33ff3fff0000000011ff1fff33ff37ff33ff3fff33773f7f33ff3fff33ff3fff33ff3fff0000000011ff1fff0000000011ffffff3377ffff33ffffff3377ffff33ffffff03ff57ff13ff5fff33ff77ff33ffffff33ffffff33ffffff33ffffff33ffffff55775f7f55ff5fff5577ffff55ffffff77777f7fffffffff7777ffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff55775f7f55ff5fff5577ffff55ffffff7777ffffffffffff7777ffffffffffff5fff5fff5fff5fffffffffffffffffff7fffffffffffffffffffffffffffffff0000000011ff1fff05ff37ff15ff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff000000001fff1fff37ff37ff3fff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff55ff57ff55ff5fff55ff77ff55ffffffffffffffffffffffffffffffffffffff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff55775f7f55ff5fff55ffffff55ffffff7f7f7f7fffffffff7fffffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff55ff5fff55ff5fff55ffffff55ffffffffffffffffffffffffffffffffffffff5fff5fff5fff5fffffffffffffffffffffffffffffffffffffffffffffffffff0000000011ffffff0000000011ffffff33773f7f33ffffff3377ffff33ffffff333f777f33ffffff33ff77ff33ffffff337f7f7f33ffffff33ffffff33ffffff0000000011ffffff0000000011ffffff3377ffff33ffffff3377ffff33ffffff33ff77ff33ffffff33ff77ff33ffffff33ffffff33ffffff33ffffff33ffffff55775f7f55ffffff5577ffff55ffffff77777f7fffffffff7777ffffffffffff7f7f7f7f7fffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff5577ffff55ffffff5577ffff55ffffff7777ffffffffffff7777ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555f777f55ffffff55ff77ff55ffffff7f7f7f7f7fffffffffffffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff55ff77ff55ffffff55ff77ff55ffffffffffffffffffffffffffffffffffffff77ff77ffffffffff77ff77ffffffffffffffffffffffffffffffffffffffffff557f7f7f55ffffff55ffffff55ffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff55ffffff55ffffff55ffffff55ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000001f1f1fff373737ff3f3f3fff000000001f1f1fff373737ff3f3f3fff000000001f1f1fff373737ff3f3f3fff3f3f3f7f3f3f3fff3f3f3fff3f3f3fff575757ff5f5f5fff777777ffffffffff5757ffff5f5fffff7777ffffffffffff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff000000001f1f1fff3737ffff3f3fffff000000001f1fffff3737ffff3f3fffff0f3f5f7f1f3f5fff3f3fffff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff575757ff5f5f5fff7777ffffffffffff5757ffff5f5fffff7777ffffffffffff5fff5fff5fff5fff7fffffffffffffffffffffffffffffffffffffffffffffff000000001f1f1fff37ff37ff3fff3fff0f5f3f7f1f5f3fff3fff3fff3fff3fff000000001fff1fff37ff37ff3fff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff575757ff5f5f5fff77ff77ffffffffff5f5fffff5f5fffff7fffffffffffffff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff5f5f5f7f5f5f5fffffffffffffffffff5f5f7f7f5f5fffffffffffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff5f5f5fff5f5f5fffffffffffffffffff5f5fffff5f5fffffffffffffffffffff5fff5fff5fff5fffffffffffffffffffffffffffffffffffffffffffffffffff000000001f1fffff373737ff3f3fffff000000001f1fffff3737ffff3f3fffff333f777f3f3fffff373f77ff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff575757ff5f5fffff777777ffffffffff5757ffff5f5fffff7777ffffffffffff77ff77ff7fffffff77ff77ffffffffffffffffffffffffffffffffffffffffff000000001f1fffff3737ffff3f3fffff000000001f1fffff3737ffff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff3f3f7f7f3f3fffff3f3fffff3f3fffff5757ffff5f5fffff7777ffffffffffff5757ffff5f5fffff7777ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555f777f5f5fffff77ff77ff7fffffff5f5f7f7f5f5fffffffffffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff575f77ff5f5fffff77ff77ffffffffff5f5fffff5f5fffffffffffffffffffff77ff77ffffffffff77ff77ffffffffffffffffffffffffffffffffffffffffff5f5f7f7f5f5fffffffffffffffffffff5f5f7f7f5f5fffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff5f5fffff5f5fffffffffffffffffffff5f5fffff5f5fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000001fff1fff373737ff3fff3fff33773f7f3fff3fff37773fff3fff3fff000000001fff1fff37ff37ff3fff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff575757ff5fff5fff777777ffffffffff7777ffff7fffffff7777ffffffffffff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff55775f7f5fff5fff7777ffff7fffffff77777f7fffffffff7777ffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff57775fff5fff5fff7777ffffffffffff7777ffffffffffff7777ffffffffffff5fff5fff5fff5fffffffffffffffffffffffffffffffffffffffffffffffffff000000001fff1fff37ff37ff3fff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff000000001fff1fff37ff37ff3fff3fff3f7f3f7f3fff3fff3fff3fff3fff3fff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff57ff57ff5fff5fff77ff77ffffffffffffffffffffffffffffffffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff5f7f5f7f5fff5fffffffffffffffffff7f7f7f7fffffffffffffffffffffffff5fff5fff5fff5fffffffffffffffffffffffffffffffffffffffffffffffffff5fff5fff5fff5fffffffffffffffffffffffffffffffffffffffffffffffffff7777777fffffffff777777ffffffffff77777f7fffffffff7777ffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff777777ffffffffff777777ffffffffff7777ffffffffffff7777ffffffffffff77ff77ffffffffff77ff77ffffffffffffffffffffffffffffffffffffffffff77777f7fffffffff7777ffffffffffff77777f7fffffffff7777ffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7777ffffffffffff7777ffffffffffff7777ffffffffffff7777ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff777f777fffffffff77ff77ffffffffff7f7f7f7fffffffffffffffffffffffff77ff77ffffffffff77ff77ffffffffffffffffffffffffffffffffffffffffff77ff77ffffffffff77ff77ffffffffffffffffffffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffff7f7f7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem packed_eq : packed = evalBvTarget rawInputs := by decide +kernel
def row (i : Label) : Row :=
  (#[0,33554431,56098815,67065855,67108863,87556095,100612095,100663295,125304831,134182911,253755391,255811455,255852543,257900415,257949695,260013951,268378111,268386303,268394495,268435455,287309823,301932543,301989887,325058559,
    335503359,356515839,369049599,522133503,522190847,524247039,526335999,536813567,859308031,859797375,859832319,863453055,863502335,863993727,872364031,872366079,872380415,872415231,926365695,926416895,926906367,930562047,939472895,1061109631,
    1061109759,1061126015,1061158911,1065303935,1073692671,1431830527,1432319871,1432354815,1433886591,1433927679,1434419071,1442797567,1442799615,1442805759,1442840575,1465341951,1465384959,1465874431,1467441151,1476351999,1600085887,1600086015,1600094079,1600126975,
    1602183039,1610571775,2004318079,2004318207,2004320127,2004353023,2004842367,2013231103,2139062143,2147483647,4294967295] : Array Row)[i.val]!
def label (i : Core) : Label :=
  (#[82,82,82,82,82,82,82,82,82,82,82,82,82,82,82,82,82,82,82,80,82,82,82,80,
    82,82,82,80,82,82,82,80,82,82,82,82,82,79,82,79,82,82,82,82,82,79,82,79,
    82,82,82,80,82,79,82,78,82,82,82,80,82,79,82,78,82,82,82,82,82,82,82,82,
    82,77,82,77,82,77,82,77,82,82,82,80,82,82,82,80,82,77,82,76,82,77,82,76,
    82,82,82,82,82,79,82,79,82,77,82,77,82,75,82,75,82,82,82,80,82,79,82,78,
    82,77,82,76,82,75,82,74,82,82,82,82,82,82,73,73,82,82,82,82,82,82,73,73,
    82,82,82,80,82,82,73,72,82,82,82,80,82,82,73,72,82,82,82,82,82,79,73,67,
    82,82,82,82,82,79,73,67,52,52,52,51,52,46,31,0,52,52,52,51,52,46,31,0,
    82,82,82,82,82,82,73,73,82,77,82,77,82,77,73,66,82,82,82,80,82,82,73,72,
    82,77,82,76,81,77,73,56,82,82,82,82,82,79,73,67,82,77,81,77,82,75,73,63,
    52,52,52,51,52,46,31,0,52,45,52,35,52,42,31,0,82,82,82,82,82,82,82,82,
    82,82,71,71,82,82,71,71,82,82,82,80,82,82,82,80,82,82,71,70,82,82,71,70,
    82,82,82,82,82,79,82,79,82,82,71,71,82,79,71,65,82,82,82,80,82,79,82,78,
    82,82,71,70,81,79,71,54,82,82,82,82,82,82,82,82,82,77,71,64,82,77,71,64,
    50,50,50,49,50,50,50,49,50,43,28,0,50,43,28,0,82,82,82,82,82,79,81,79,
    82,77,71,64,82,75,71,63,50,50,50,49,50,44,50,33,50,43,28,0,50,42,28,0,
    82,82,82,82,82,82,73,73,82,82,71,71,82,82,69,69,82,82,82,80,82,82,73,72,
    82,82,71,70,82,82,69,68,82,82,82,82,82,79,73,67,82,81,71,71,82,79,69,63,
    52,52,52,51,52,46,31,0,52,52,30,13,52,46,27,0,82,82,82,82,82,81,73,73,
    82,77,71,64,82,77,69,63,50,50,50,49,50,50,29,11,50,43,28,0,50,43,27,0,
    82,82,82,82,82,79,73,67,82,77,71,64,82,75,69,63,48,48,48,47,48,42,27,0,
    48,42,27,0,48,42,27,0,82,82,82,82,82,82,82,82,82,82,82,82,62,62,62,62,
    82,82,82,80,82,82,82,80,82,82,82,80,62,62,62,58,82,82,82,82,82,79,82,79,
    82,82,82,82,62,61,62,61,82,82,82,80,82,79,82,78,82,82,81,80,62,61,62,54,
    82,82,82,82,82,82,82,82,82,77,82,77,62,57,62,57,82,82,82,80,82,82,81,80,
    82,77,82,76,62,57,62,56,41,41,41,41,41,40,41,40,41,36,41,36,22,0,22,0,
    41,41,41,37,41,40,41,33,41,36,41,35,22,0,22,0,82,82,82,82,82,82,73,73,
    82,82,82,82,62,62,60,60,82,82,82,80,82,82,73,72,82,81,82,80,62,62,60,56,
    82,82,82,82,82,79,73,67,82,82,82,82,62,61,60,59,52,52,52,51,52,46,31,0,
    52,52,52,51,26,6,21,0,82,82,82,81,82,82,73,73,82,77,82,77,62,57,60,56,
    82,82,82,80,82,82,73,72,82,77,82,76,62,57,60,56,41,41,41,41,41,40,24,3,
    41,36,41,36,22,0,21,0,39,39,39,35,39,38,21,0,39,35,39,35,21,0,21,0,
    82,82,82,82,82,82,82,82,82,82,71,71,62,62,55,55,82,82,82,80,82,81,82,80,
    82,82,71,70,62,62,55,54,82,82,82,81,82,79,82,79,82,82,71,71,62,61,55,54,
    82,82,82,80,82,79,82,78,82,82,71,70,62,61,55,54,82,82,82,82,82,82,82,82,
    82,77,71,64,62,57,55,53,50,50,50,49,50,50,50,49,50,43,28,0,25,5,20,0,
    41,41,41,41,41,40,41,40,41,36,23,2,22,0,20,0,34,34,34,33,34,33,34,33,
    34,32,20,0,20,0,20,0,19,19,19,19,19,19,18,18,19,19,14,14,7,7,0,0,
    19,19,19,15,19,19,18,11,19,19,14,13,7,7,0,0,19,19,19,19,19,9,18,3,
    19,19,14,14,7,6,0,0,17,17,17,13,17,6,16,0,17,17,13,13,6,6,0,0,
    19,19,19,19,19,19,18,18,19,8,14,2,7,5,0,0,12,12,12,11,12,12,11,11,
    12,5,10,0,5,5,0,0,4,4,4,4,4,3,3,3,4,2,2,2,1,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Array Label)[i.val]!
def representative (i : Label) : Core :=
  (#[183,1004,875,743,992,861,701,908,969,933,986,471,976,443,906,915,950,944,902,896,862,702,620,874,
    742,860,700,446,346,470,442,182,889,375,880,251,617,627,757,752,613,608,253,345,373,249,181,499,
    496,339,336,179,176,847,319,782,223,589,543,687,654,557,524,239,331,303,207,167,415,398,283,266,
    151,134,127,109,91,73,55,37,19,220,0] : Array Core)[i.val]!
def separated (i : Fin 45) : Label :=
  (#[4,7,8,9,12,14,15,17,18,22,23,24,25,26,28,29,30,31,34,36,37,39,40,43,
    44,45,46,48,49,51,55,57,58,60,61,64,65,66,67,69,70,72,75,76,78] : Array Label)[i.val]!
def message (i : Label) : Fin 256 :=
  (#[0,240,226,225,216,212,180,204,177,172,169,165,163,156,153,150,232,228,108,236,149,141,78,75,
    120,114,198,195,106,105,102,99,92,90,89,86,60,54,77,71,15,79,45,39,83,30,197,209,
    147,210,211,135,199,29,23,202,101,53,51,166,178,142,206,201,139,46,85,170,184,154,43,203,
    58,186,27,116,113,117,57,174,59,254,255] : Array (Fin 256))[i.val]!


private theorem joinChunks {P : Nat → Prop} {start a b : Nat}
    (lo : ∀ i : Fin a, P (start+i.val))
    (hi : ∀ i : Fin b, P (start+a+i.val)) :
    ∀ j : Fin (a+b), P (start+j.val) := by
  intro j
  by_cases h : j.val < a
  · exact lo ⟨j.val,h⟩
  · have t := hi ⟨j.val-a,by have := j.isLt; omega⟩
    dsimp only at t
    rwa [show start+a+(j.val-a) = start+j.val by omega] at t

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

private def distinctRow (i : Nat) : Prop := ∀ b : Label, row (Fin.ofNat 83 i) = row b → Fin.ofNat 83 i = b

private theorem distinctRow_0_2 : ∀ i : Fin 2, distinctRow (0+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_2_5 : ∀ i : Fin 3, distinctRow (2+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_0_5 : ∀ i : Fin 5, distinctRow (0+i.val) := joinChunks (P := distinctRow) (start := 0) (a := 2) (b := 3) distinctRow_0_2 distinctRow_2_5

private theorem distinctRow_5_7 : ∀ i : Fin 2, distinctRow (5+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_7_10 : ∀ i : Fin 3, distinctRow (7+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_5_10 : ∀ i : Fin 5, distinctRow (5+i.val) := joinChunks (P := distinctRow) (start := 5) (a := 2) (b := 3) distinctRow_5_7 distinctRow_7_10

private theorem distinctRow_0_10 : ∀ i : Fin 10, distinctRow (0+i.val) := joinChunks (P := distinctRow) (start := 0) (a := 5) (b := 5) distinctRow_0_5 distinctRow_5_10

private theorem distinctRow_10_12 : ∀ i : Fin 2, distinctRow (10+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_12_15 : ∀ i : Fin 3, distinctRow (12+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_10_15 : ∀ i : Fin 5, distinctRow (10+i.val) := joinChunks (P := distinctRow) (start := 10) (a := 2) (b := 3) distinctRow_10_12 distinctRow_12_15

private theorem distinctRow_15_17 : ∀ i : Fin 2, distinctRow (15+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_17_20 : ∀ i : Fin 3, distinctRow (17+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_15_20 : ∀ i : Fin 5, distinctRow (15+i.val) := joinChunks (P := distinctRow) (start := 15) (a := 2) (b := 3) distinctRow_15_17 distinctRow_17_20

private theorem distinctRow_10_20 : ∀ i : Fin 10, distinctRow (10+i.val) := joinChunks (P := distinctRow) (start := 10) (a := 5) (b := 5) distinctRow_10_15 distinctRow_15_20

private theorem distinctRow_0_20 : ∀ i : Fin 20, distinctRow (0+i.val) := joinChunks (P := distinctRow) (start := 0) (a := 10) (b := 10) distinctRow_0_10 distinctRow_10_20

private theorem distinctRow_20_22 : ∀ i : Fin 2, distinctRow (20+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_22_25 : ∀ i : Fin 3, distinctRow (22+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_20_25 : ∀ i : Fin 5, distinctRow (20+i.val) := joinChunks (P := distinctRow) (start := 20) (a := 2) (b := 3) distinctRow_20_22 distinctRow_22_25

private theorem distinctRow_25_27 : ∀ i : Fin 2, distinctRow (25+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_27_30 : ∀ i : Fin 3, distinctRow (27+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_25_30 : ∀ i : Fin 5, distinctRow (25+i.val) := joinChunks (P := distinctRow) (start := 25) (a := 2) (b := 3) distinctRow_25_27 distinctRow_27_30

private theorem distinctRow_20_30 : ∀ i : Fin 10, distinctRow (20+i.val) := joinChunks (P := distinctRow) (start := 20) (a := 5) (b := 5) distinctRow_20_25 distinctRow_25_30

private theorem distinctRow_30_32 : ∀ i : Fin 2, distinctRow (30+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_32_35 : ∀ i : Fin 3, distinctRow (32+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_30_35 : ∀ i : Fin 5, distinctRow (30+i.val) := joinChunks (P := distinctRow) (start := 30) (a := 2) (b := 3) distinctRow_30_32 distinctRow_32_35

private theorem distinctRow_35_38 : ∀ i : Fin 3, distinctRow (35+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_38_41 : ∀ i : Fin 3, distinctRow (38+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_35_41 : ∀ i : Fin 6, distinctRow (35+i.val) := joinChunks (P := distinctRow) (start := 35) (a := 3) (b := 3) distinctRow_35_38 distinctRow_38_41

private theorem distinctRow_30_41 : ∀ i : Fin 11, distinctRow (30+i.val) := joinChunks (P := distinctRow) (start := 30) (a := 5) (b := 6) distinctRow_30_35 distinctRow_35_41

private theorem distinctRow_20_41 : ∀ i : Fin 21, distinctRow (20+i.val) := joinChunks (P := distinctRow) (start := 20) (a := 10) (b := 11) distinctRow_20_30 distinctRow_30_41

private theorem distinctRow_0_41 : ∀ i : Fin 41, distinctRow (0+i.val) := joinChunks (P := distinctRow) (start := 0) (a := 20) (b := 21) distinctRow_0_20 distinctRow_20_41

private theorem distinctRow_41_43 : ∀ i : Fin 2, distinctRow (41+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_43_46 : ∀ i : Fin 3, distinctRow (43+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_41_46 : ∀ i : Fin 5, distinctRow (41+i.val) := joinChunks (P := distinctRow) (start := 41) (a := 2) (b := 3) distinctRow_41_43 distinctRow_43_46

private theorem distinctRow_46_48 : ∀ i : Fin 2, distinctRow (46+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_48_51 : ∀ i : Fin 3, distinctRow (48+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_46_51 : ∀ i : Fin 5, distinctRow (46+i.val) := joinChunks (P := distinctRow) (start := 46) (a := 2) (b := 3) distinctRow_46_48 distinctRow_48_51

private theorem distinctRow_41_51 : ∀ i : Fin 10, distinctRow (41+i.val) := joinChunks (P := distinctRow) (start := 41) (a := 5) (b := 5) distinctRow_41_46 distinctRow_46_51

private theorem distinctRow_51_53 : ∀ i : Fin 2, distinctRow (51+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_53_56 : ∀ i : Fin 3, distinctRow (53+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_51_56 : ∀ i : Fin 5, distinctRow (51+i.val) := joinChunks (P := distinctRow) (start := 51) (a := 2) (b := 3) distinctRow_51_53 distinctRow_53_56

private theorem distinctRow_56_59 : ∀ i : Fin 3, distinctRow (56+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_59_62 : ∀ i : Fin 3, distinctRow (59+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_56_62 : ∀ i : Fin 6, distinctRow (56+i.val) := joinChunks (P := distinctRow) (start := 56) (a := 3) (b := 3) distinctRow_56_59 distinctRow_59_62

private theorem distinctRow_51_62 : ∀ i : Fin 11, distinctRow (51+i.val) := joinChunks (P := distinctRow) (start := 51) (a := 5) (b := 6) distinctRow_51_56 distinctRow_56_62

private theorem distinctRow_41_62 : ∀ i : Fin 21, distinctRow (41+i.val) := joinChunks (P := distinctRow) (start := 41) (a := 10) (b := 11) distinctRow_41_51 distinctRow_51_62

private theorem distinctRow_62_64 : ∀ i : Fin 2, distinctRow (62+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_64_67 : ∀ i : Fin 3, distinctRow (64+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_62_67 : ∀ i : Fin 5, distinctRow (62+i.val) := joinChunks (P := distinctRow) (start := 62) (a := 2) (b := 3) distinctRow_62_64 distinctRow_64_67

private theorem distinctRow_67_69 : ∀ i : Fin 2, distinctRow (67+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_69_72 : ∀ i : Fin 3, distinctRow (69+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_67_72 : ∀ i : Fin 5, distinctRow (67+i.val) := joinChunks (P := distinctRow) (start := 67) (a := 2) (b := 3) distinctRow_67_69 distinctRow_69_72

private theorem distinctRow_62_72 : ∀ i : Fin 10, distinctRow (62+i.val) := joinChunks (P := distinctRow) (start := 62) (a := 5) (b := 5) distinctRow_62_67 distinctRow_67_72

private theorem distinctRow_72_74 : ∀ i : Fin 2, distinctRow (72+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_74_77 : ∀ i : Fin 3, distinctRow (74+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_72_77 : ∀ i : Fin 5, distinctRow (72+i.val) := joinChunks (P := distinctRow) (start := 72) (a := 2) (b := 3) distinctRow_72_74 distinctRow_74_77

private theorem distinctRow_77_80 : ∀ i : Fin 3, distinctRow (77+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_80_83 : ∀ i : Fin 3, distinctRow (80+i.val) := by unfold distinctRow; decide +kernel

private theorem distinctRow_77_83 : ∀ i : Fin 6, distinctRow (77+i.val) := joinChunks (P := distinctRow) (start := 77) (a := 3) (b := 3) distinctRow_77_80 distinctRow_80_83

private theorem distinctRow_72_83 : ∀ i : Fin 11, distinctRow (72+i.val) := joinChunks (P := distinctRow) (start := 72) (a := 5) (b := 6) distinctRow_72_77 distinctRow_77_83

private theorem distinctRow_62_83 : ∀ i : Fin 21, distinctRow (62+i.val) := joinChunks (P := distinctRow) (start := 62) (a := 10) (b := 11) distinctRow_62_72 distinctRow_72_83

private theorem distinctRow_41_83 : ∀ i : Fin 42, distinctRow (41+i.val) := joinChunks (P := distinctRow) (start := 41) (a := 21) (b := 21) distinctRow_41_62 distinctRow_62_83

private theorem distinctRow_0_83 : ∀ i : Fin 83, distinctRow (0+i.val) := joinChunks (P := distinctRow) (start := 0) (a := 41) (b := 42) distinctRow_0_41 distinctRow_41_83

theorem distinct : Function.Injective row := by
  intro a b h
  have t := distinctRow_0_83 a
  simpa [distinctRow,Fin.ofNat, Nat.mod_eq_of_lt a.isLt] using t b (by simpa [Fin.ofNat, Nat.mod_eq_of_lt a.isLt] using h)

theorem section_label : ∀ i, label (representative i) = i := by decide +kernel

private def rowSlice (i : Nat) : Prop := let c := Fin.ofNat 1024 i; row (label c) = BitVec.ofNat 32 (packed.toNat >>> (32*c.val))

private theorem rowSlice_0_8 : ∀ i : Fin 8, rowSlice (0+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_8_16 : ∀ i : Fin 8, rowSlice (8+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_0_16 : ∀ i : Fin 16, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 8) (b := 8) rowSlice_0_8 rowSlice_8_16

private theorem rowSlice_16_24 : ∀ i : Fin 8, rowSlice (16+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_24_32 : ∀ i : Fin 8, rowSlice (24+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_16_32 : ∀ i : Fin 16, rowSlice (16+i.val) := joinChunks (P := rowSlice) (start := 16) (a := 8) (b := 8) rowSlice_16_24 rowSlice_24_32

private theorem rowSlice_0_32 : ∀ i : Fin 32, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 16) (b := 16) rowSlice_0_16 rowSlice_16_32

private theorem rowSlice_32_40 : ∀ i : Fin 8, rowSlice (32+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_40_48 : ∀ i : Fin 8, rowSlice (40+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_32_48 : ∀ i : Fin 16, rowSlice (32+i.val) := joinChunks (P := rowSlice) (start := 32) (a := 8) (b := 8) rowSlice_32_40 rowSlice_40_48

private theorem rowSlice_48_56 : ∀ i : Fin 8, rowSlice (48+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_56_64 : ∀ i : Fin 8, rowSlice (56+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_48_64 : ∀ i : Fin 16, rowSlice (48+i.val) := joinChunks (P := rowSlice) (start := 48) (a := 8) (b := 8) rowSlice_48_56 rowSlice_56_64

private theorem rowSlice_32_64 : ∀ i : Fin 32, rowSlice (32+i.val) := joinChunks (P := rowSlice) (start := 32) (a := 16) (b := 16) rowSlice_32_48 rowSlice_48_64

private theorem rowSlice_0_64 : ∀ i : Fin 64, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 32) (b := 32) rowSlice_0_32 rowSlice_32_64

private theorem rowSlice_64_72 : ∀ i : Fin 8, rowSlice (64+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_72_80 : ∀ i : Fin 8, rowSlice (72+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_64_80 : ∀ i : Fin 16, rowSlice (64+i.val) := joinChunks (P := rowSlice) (start := 64) (a := 8) (b := 8) rowSlice_64_72 rowSlice_72_80

private theorem rowSlice_80_88 : ∀ i : Fin 8, rowSlice (80+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_88_96 : ∀ i : Fin 8, rowSlice (88+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_80_96 : ∀ i : Fin 16, rowSlice (80+i.val) := joinChunks (P := rowSlice) (start := 80) (a := 8) (b := 8) rowSlice_80_88 rowSlice_88_96

private theorem rowSlice_64_96 : ∀ i : Fin 32, rowSlice (64+i.val) := joinChunks (P := rowSlice) (start := 64) (a := 16) (b := 16) rowSlice_64_80 rowSlice_80_96

private theorem rowSlice_96_104 : ∀ i : Fin 8, rowSlice (96+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_104_112 : ∀ i : Fin 8, rowSlice (104+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_96_112 : ∀ i : Fin 16, rowSlice (96+i.val) := joinChunks (P := rowSlice) (start := 96) (a := 8) (b := 8) rowSlice_96_104 rowSlice_104_112

private theorem rowSlice_112_120 : ∀ i : Fin 8, rowSlice (112+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_120_128 : ∀ i : Fin 8, rowSlice (120+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_112_128 : ∀ i : Fin 16, rowSlice (112+i.val) := joinChunks (P := rowSlice) (start := 112) (a := 8) (b := 8) rowSlice_112_120 rowSlice_120_128

private theorem rowSlice_96_128 : ∀ i : Fin 32, rowSlice (96+i.val) := joinChunks (P := rowSlice) (start := 96) (a := 16) (b := 16) rowSlice_96_112 rowSlice_112_128

private theorem rowSlice_64_128 : ∀ i : Fin 64, rowSlice (64+i.val) := joinChunks (P := rowSlice) (start := 64) (a := 32) (b := 32) rowSlice_64_96 rowSlice_96_128

private theorem rowSlice_0_128 : ∀ i : Fin 128, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 64) (b := 64) rowSlice_0_64 rowSlice_64_128

private theorem rowSlice_128_136 : ∀ i : Fin 8, rowSlice (128+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_136_144 : ∀ i : Fin 8, rowSlice (136+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_128_144 : ∀ i : Fin 16, rowSlice (128+i.val) := joinChunks (P := rowSlice) (start := 128) (a := 8) (b := 8) rowSlice_128_136 rowSlice_136_144

private theorem rowSlice_144_152 : ∀ i : Fin 8, rowSlice (144+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_152_160 : ∀ i : Fin 8, rowSlice (152+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_144_160 : ∀ i : Fin 16, rowSlice (144+i.val) := joinChunks (P := rowSlice) (start := 144) (a := 8) (b := 8) rowSlice_144_152 rowSlice_152_160

private theorem rowSlice_128_160 : ∀ i : Fin 32, rowSlice (128+i.val) := joinChunks (P := rowSlice) (start := 128) (a := 16) (b := 16) rowSlice_128_144 rowSlice_144_160

private theorem rowSlice_160_168 : ∀ i : Fin 8, rowSlice (160+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_168_176 : ∀ i : Fin 8, rowSlice (168+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_160_176 : ∀ i : Fin 16, rowSlice (160+i.val) := joinChunks (P := rowSlice) (start := 160) (a := 8) (b := 8) rowSlice_160_168 rowSlice_168_176

private theorem rowSlice_176_184 : ∀ i : Fin 8, rowSlice (176+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_184_192 : ∀ i : Fin 8, rowSlice (184+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_176_192 : ∀ i : Fin 16, rowSlice (176+i.val) := joinChunks (P := rowSlice) (start := 176) (a := 8) (b := 8) rowSlice_176_184 rowSlice_184_192

private theorem rowSlice_160_192 : ∀ i : Fin 32, rowSlice (160+i.val) := joinChunks (P := rowSlice) (start := 160) (a := 16) (b := 16) rowSlice_160_176 rowSlice_176_192

private theorem rowSlice_128_192 : ∀ i : Fin 64, rowSlice (128+i.val) := joinChunks (P := rowSlice) (start := 128) (a := 32) (b := 32) rowSlice_128_160 rowSlice_160_192

private theorem rowSlice_192_200 : ∀ i : Fin 8, rowSlice (192+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_200_208 : ∀ i : Fin 8, rowSlice (200+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_192_208 : ∀ i : Fin 16, rowSlice (192+i.val) := joinChunks (P := rowSlice) (start := 192) (a := 8) (b := 8) rowSlice_192_200 rowSlice_200_208

private theorem rowSlice_208_216 : ∀ i : Fin 8, rowSlice (208+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_216_224 : ∀ i : Fin 8, rowSlice (216+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_208_224 : ∀ i : Fin 16, rowSlice (208+i.val) := joinChunks (P := rowSlice) (start := 208) (a := 8) (b := 8) rowSlice_208_216 rowSlice_216_224

private theorem rowSlice_192_224 : ∀ i : Fin 32, rowSlice (192+i.val) := joinChunks (P := rowSlice) (start := 192) (a := 16) (b := 16) rowSlice_192_208 rowSlice_208_224

private theorem rowSlice_224_232 : ∀ i : Fin 8, rowSlice (224+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_232_240 : ∀ i : Fin 8, rowSlice (232+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_224_240 : ∀ i : Fin 16, rowSlice (224+i.val) := joinChunks (P := rowSlice) (start := 224) (a := 8) (b := 8) rowSlice_224_232 rowSlice_232_240

private theorem rowSlice_240_248 : ∀ i : Fin 8, rowSlice (240+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_248_256 : ∀ i : Fin 8, rowSlice (248+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_240_256 : ∀ i : Fin 16, rowSlice (240+i.val) := joinChunks (P := rowSlice) (start := 240) (a := 8) (b := 8) rowSlice_240_248 rowSlice_248_256

private theorem rowSlice_224_256 : ∀ i : Fin 32, rowSlice (224+i.val) := joinChunks (P := rowSlice) (start := 224) (a := 16) (b := 16) rowSlice_224_240 rowSlice_240_256

private theorem rowSlice_192_256 : ∀ i : Fin 64, rowSlice (192+i.val) := joinChunks (P := rowSlice) (start := 192) (a := 32) (b := 32) rowSlice_192_224 rowSlice_224_256

private theorem rowSlice_128_256 : ∀ i : Fin 128, rowSlice (128+i.val) := joinChunks (P := rowSlice) (start := 128) (a := 64) (b := 64) rowSlice_128_192 rowSlice_192_256

private theorem rowSlice_0_256 : ∀ i : Fin 256, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 128) (b := 128) rowSlice_0_128 rowSlice_128_256

private theorem rowSlice_256_264 : ∀ i : Fin 8, rowSlice (256+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_264_272 : ∀ i : Fin 8, rowSlice (264+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_256_272 : ∀ i : Fin 16, rowSlice (256+i.val) := joinChunks (P := rowSlice) (start := 256) (a := 8) (b := 8) rowSlice_256_264 rowSlice_264_272

private theorem rowSlice_272_280 : ∀ i : Fin 8, rowSlice (272+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_280_288 : ∀ i : Fin 8, rowSlice (280+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_272_288 : ∀ i : Fin 16, rowSlice (272+i.val) := joinChunks (P := rowSlice) (start := 272) (a := 8) (b := 8) rowSlice_272_280 rowSlice_280_288

private theorem rowSlice_256_288 : ∀ i : Fin 32, rowSlice (256+i.val) := joinChunks (P := rowSlice) (start := 256) (a := 16) (b := 16) rowSlice_256_272 rowSlice_272_288

private theorem rowSlice_288_296 : ∀ i : Fin 8, rowSlice (288+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_296_304 : ∀ i : Fin 8, rowSlice (296+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_288_304 : ∀ i : Fin 16, rowSlice (288+i.val) := joinChunks (P := rowSlice) (start := 288) (a := 8) (b := 8) rowSlice_288_296 rowSlice_296_304

private theorem rowSlice_304_312 : ∀ i : Fin 8, rowSlice (304+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_312_320 : ∀ i : Fin 8, rowSlice (312+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_304_320 : ∀ i : Fin 16, rowSlice (304+i.val) := joinChunks (P := rowSlice) (start := 304) (a := 8) (b := 8) rowSlice_304_312 rowSlice_312_320

private theorem rowSlice_288_320 : ∀ i : Fin 32, rowSlice (288+i.val) := joinChunks (P := rowSlice) (start := 288) (a := 16) (b := 16) rowSlice_288_304 rowSlice_304_320

private theorem rowSlice_256_320 : ∀ i : Fin 64, rowSlice (256+i.val) := joinChunks (P := rowSlice) (start := 256) (a := 32) (b := 32) rowSlice_256_288 rowSlice_288_320

private theorem rowSlice_320_328 : ∀ i : Fin 8, rowSlice (320+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_328_336 : ∀ i : Fin 8, rowSlice (328+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_320_336 : ∀ i : Fin 16, rowSlice (320+i.val) := joinChunks (P := rowSlice) (start := 320) (a := 8) (b := 8) rowSlice_320_328 rowSlice_328_336

private theorem rowSlice_336_344 : ∀ i : Fin 8, rowSlice (336+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_344_352 : ∀ i : Fin 8, rowSlice (344+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_336_352 : ∀ i : Fin 16, rowSlice (336+i.val) := joinChunks (P := rowSlice) (start := 336) (a := 8) (b := 8) rowSlice_336_344 rowSlice_344_352

private theorem rowSlice_320_352 : ∀ i : Fin 32, rowSlice (320+i.val) := joinChunks (P := rowSlice) (start := 320) (a := 16) (b := 16) rowSlice_320_336 rowSlice_336_352

private theorem rowSlice_352_360 : ∀ i : Fin 8, rowSlice (352+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_360_368 : ∀ i : Fin 8, rowSlice (360+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_352_368 : ∀ i : Fin 16, rowSlice (352+i.val) := joinChunks (P := rowSlice) (start := 352) (a := 8) (b := 8) rowSlice_352_360 rowSlice_360_368

private theorem rowSlice_368_376 : ∀ i : Fin 8, rowSlice (368+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_376_384 : ∀ i : Fin 8, rowSlice (376+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_368_384 : ∀ i : Fin 16, rowSlice (368+i.val) := joinChunks (P := rowSlice) (start := 368) (a := 8) (b := 8) rowSlice_368_376 rowSlice_376_384

private theorem rowSlice_352_384 : ∀ i : Fin 32, rowSlice (352+i.val) := joinChunks (P := rowSlice) (start := 352) (a := 16) (b := 16) rowSlice_352_368 rowSlice_368_384

private theorem rowSlice_320_384 : ∀ i : Fin 64, rowSlice (320+i.val) := joinChunks (P := rowSlice) (start := 320) (a := 32) (b := 32) rowSlice_320_352 rowSlice_352_384

private theorem rowSlice_256_384 : ∀ i : Fin 128, rowSlice (256+i.val) := joinChunks (P := rowSlice) (start := 256) (a := 64) (b := 64) rowSlice_256_320 rowSlice_320_384

private theorem rowSlice_384_392 : ∀ i : Fin 8, rowSlice (384+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_392_400 : ∀ i : Fin 8, rowSlice (392+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_384_400 : ∀ i : Fin 16, rowSlice (384+i.val) := joinChunks (P := rowSlice) (start := 384) (a := 8) (b := 8) rowSlice_384_392 rowSlice_392_400

private theorem rowSlice_400_408 : ∀ i : Fin 8, rowSlice (400+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_408_416 : ∀ i : Fin 8, rowSlice (408+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_400_416 : ∀ i : Fin 16, rowSlice (400+i.val) := joinChunks (P := rowSlice) (start := 400) (a := 8) (b := 8) rowSlice_400_408 rowSlice_408_416

private theorem rowSlice_384_416 : ∀ i : Fin 32, rowSlice (384+i.val) := joinChunks (P := rowSlice) (start := 384) (a := 16) (b := 16) rowSlice_384_400 rowSlice_400_416

private theorem rowSlice_416_424 : ∀ i : Fin 8, rowSlice (416+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_424_432 : ∀ i : Fin 8, rowSlice (424+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_416_432 : ∀ i : Fin 16, rowSlice (416+i.val) := joinChunks (P := rowSlice) (start := 416) (a := 8) (b := 8) rowSlice_416_424 rowSlice_424_432

private theorem rowSlice_432_440 : ∀ i : Fin 8, rowSlice (432+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_440_448 : ∀ i : Fin 8, rowSlice (440+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_432_448 : ∀ i : Fin 16, rowSlice (432+i.val) := joinChunks (P := rowSlice) (start := 432) (a := 8) (b := 8) rowSlice_432_440 rowSlice_440_448

private theorem rowSlice_416_448 : ∀ i : Fin 32, rowSlice (416+i.val) := joinChunks (P := rowSlice) (start := 416) (a := 16) (b := 16) rowSlice_416_432 rowSlice_432_448

private theorem rowSlice_384_448 : ∀ i : Fin 64, rowSlice (384+i.val) := joinChunks (P := rowSlice) (start := 384) (a := 32) (b := 32) rowSlice_384_416 rowSlice_416_448

private theorem rowSlice_448_456 : ∀ i : Fin 8, rowSlice (448+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_456_464 : ∀ i : Fin 8, rowSlice (456+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_448_464 : ∀ i : Fin 16, rowSlice (448+i.val) := joinChunks (P := rowSlice) (start := 448) (a := 8) (b := 8) rowSlice_448_456 rowSlice_456_464

private theorem rowSlice_464_472 : ∀ i : Fin 8, rowSlice (464+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_472_480 : ∀ i : Fin 8, rowSlice (472+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_464_480 : ∀ i : Fin 16, rowSlice (464+i.val) := joinChunks (P := rowSlice) (start := 464) (a := 8) (b := 8) rowSlice_464_472 rowSlice_472_480

private theorem rowSlice_448_480 : ∀ i : Fin 32, rowSlice (448+i.val) := joinChunks (P := rowSlice) (start := 448) (a := 16) (b := 16) rowSlice_448_464 rowSlice_464_480

private theorem rowSlice_480_488 : ∀ i : Fin 8, rowSlice (480+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_488_496 : ∀ i : Fin 8, rowSlice (488+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_480_496 : ∀ i : Fin 16, rowSlice (480+i.val) := joinChunks (P := rowSlice) (start := 480) (a := 8) (b := 8) rowSlice_480_488 rowSlice_488_496

private theorem rowSlice_496_504 : ∀ i : Fin 8, rowSlice (496+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_504_512 : ∀ i : Fin 8, rowSlice (504+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_496_512 : ∀ i : Fin 16, rowSlice (496+i.val) := joinChunks (P := rowSlice) (start := 496) (a := 8) (b := 8) rowSlice_496_504 rowSlice_504_512

private theorem rowSlice_480_512 : ∀ i : Fin 32, rowSlice (480+i.val) := joinChunks (P := rowSlice) (start := 480) (a := 16) (b := 16) rowSlice_480_496 rowSlice_496_512

private theorem rowSlice_448_512 : ∀ i : Fin 64, rowSlice (448+i.val) := joinChunks (P := rowSlice) (start := 448) (a := 32) (b := 32) rowSlice_448_480 rowSlice_480_512

private theorem rowSlice_384_512 : ∀ i : Fin 128, rowSlice (384+i.val) := joinChunks (P := rowSlice) (start := 384) (a := 64) (b := 64) rowSlice_384_448 rowSlice_448_512

private theorem rowSlice_256_512 : ∀ i : Fin 256, rowSlice (256+i.val) := joinChunks (P := rowSlice) (start := 256) (a := 128) (b := 128) rowSlice_256_384 rowSlice_384_512

private theorem rowSlice_0_512 : ∀ i : Fin 512, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 256) (b := 256) rowSlice_0_256 rowSlice_256_512

private theorem rowSlice_512_520 : ∀ i : Fin 8, rowSlice (512+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_520_528 : ∀ i : Fin 8, rowSlice (520+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_512_528 : ∀ i : Fin 16, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 8) (b := 8) rowSlice_512_520 rowSlice_520_528

private theorem rowSlice_528_536 : ∀ i : Fin 8, rowSlice (528+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_536_544 : ∀ i : Fin 8, rowSlice (536+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_528_544 : ∀ i : Fin 16, rowSlice (528+i.val) := joinChunks (P := rowSlice) (start := 528) (a := 8) (b := 8) rowSlice_528_536 rowSlice_536_544

private theorem rowSlice_512_544 : ∀ i : Fin 32, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 16) (b := 16) rowSlice_512_528 rowSlice_528_544

private theorem rowSlice_544_552 : ∀ i : Fin 8, rowSlice (544+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_552_560 : ∀ i : Fin 8, rowSlice (552+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_544_560 : ∀ i : Fin 16, rowSlice (544+i.val) := joinChunks (P := rowSlice) (start := 544) (a := 8) (b := 8) rowSlice_544_552 rowSlice_552_560

private theorem rowSlice_560_568 : ∀ i : Fin 8, rowSlice (560+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_568_576 : ∀ i : Fin 8, rowSlice (568+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_560_576 : ∀ i : Fin 16, rowSlice (560+i.val) := joinChunks (P := rowSlice) (start := 560) (a := 8) (b := 8) rowSlice_560_568 rowSlice_568_576

private theorem rowSlice_544_576 : ∀ i : Fin 32, rowSlice (544+i.val) := joinChunks (P := rowSlice) (start := 544) (a := 16) (b := 16) rowSlice_544_560 rowSlice_560_576

private theorem rowSlice_512_576 : ∀ i : Fin 64, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 32) (b := 32) rowSlice_512_544 rowSlice_544_576

private theorem rowSlice_576_584 : ∀ i : Fin 8, rowSlice (576+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_584_592 : ∀ i : Fin 8, rowSlice (584+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_576_592 : ∀ i : Fin 16, rowSlice (576+i.val) := joinChunks (P := rowSlice) (start := 576) (a := 8) (b := 8) rowSlice_576_584 rowSlice_584_592

private theorem rowSlice_592_600 : ∀ i : Fin 8, rowSlice (592+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_600_608 : ∀ i : Fin 8, rowSlice (600+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_592_608 : ∀ i : Fin 16, rowSlice (592+i.val) := joinChunks (P := rowSlice) (start := 592) (a := 8) (b := 8) rowSlice_592_600 rowSlice_600_608

private theorem rowSlice_576_608 : ∀ i : Fin 32, rowSlice (576+i.val) := joinChunks (P := rowSlice) (start := 576) (a := 16) (b := 16) rowSlice_576_592 rowSlice_592_608

private theorem rowSlice_608_616 : ∀ i : Fin 8, rowSlice (608+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_616_624 : ∀ i : Fin 8, rowSlice (616+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_608_624 : ∀ i : Fin 16, rowSlice (608+i.val) := joinChunks (P := rowSlice) (start := 608) (a := 8) (b := 8) rowSlice_608_616 rowSlice_616_624

private theorem rowSlice_624_632 : ∀ i : Fin 8, rowSlice (624+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_632_640 : ∀ i : Fin 8, rowSlice (632+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_624_640 : ∀ i : Fin 16, rowSlice (624+i.val) := joinChunks (P := rowSlice) (start := 624) (a := 8) (b := 8) rowSlice_624_632 rowSlice_632_640

private theorem rowSlice_608_640 : ∀ i : Fin 32, rowSlice (608+i.val) := joinChunks (P := rowSlice) (start := 608) (a := 16) (b := 16) rowSlice_608_624 rowSlice_624_640

private theorem rowSlice_576_640 : ∀ i : Fin 64, rowSlice (576+i.val) := joinChunks (P := rowSlice) (start := 576) (a := 32) (b := 32) rowSlice_576_608 rowSlice_608_640

private theorem rowSlice_512_640 : ∀ i : Fin 128, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 64) (b := 64) rowSlice_512_576 rowSlice_576_640

private theorem rowSlice_640_648 : ∀ i : Fin 8, rowSlice (640+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_648_656 : ∀ i : Fin 8, rowSlice (648+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_640_656 : ∀ i : Fin 16, rowSlice (640+i.val) := joinChunks (P := rowSlice) (start := 640) (a := 8) (b := 8) rowSlice_640_648 rowSlice_648_656

private theorem rowSlice_656_664 : ∀ i : Fin 8, rowSlice (656+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_664_672 : ∀ i : Fin 8, rowSlice (664+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_656_672 : ∀ i : Fin 16, rowSlice (656+i.val) := joinChunks (P := rowSlice) (start := 656) (a := 8) (b := 8) rowSlice_656_664 rowSlice_664_672

private theorem rowSlice_640_672 : ∀ i : Fin 32, rowSlice (640+i.val) := joinChunks (P := rowSlice) (start := 640) (a := 16) (b := 16) rowSlice_640_656 rowSlice_656_672

private theorem rowSlice_672_680 : ∀ i : Fin 8, rowSlice (672+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_680_688 : ∀ i : Fin 8, rowSlice (680+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_672_688 : ∀ i : Fin 16, rowSlice (672+i.val) := joinChunks (P := rowSlice) (start := 672) (a := 8) (b := 8) rowSlice_672_680 rowSlice_680_688

private theorem rowSlice_688_696 : ∀ i : Fin 8, rowSlice (688+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_696_704 : ∀ i : Fin 8, rowSlice (696+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_688_704 : ∀ i : Fin 16, rowSlice (688+i.val) := joinChunks (P := rowSlice) (start := 688) (a := 8) (b := 8) rowSlice_688_696 rowSlice_696_704

private theorem rowSlice_672_704 : ∀ i : Fin 32, rowSlice (672+i.val) := joinChunks (P := rowSlice) (start := 672) (a := 16) (b := 16) rowSlice_672_688 rowSlice_688_704

private theorem rowSlice_640_704 : ∀ i : Fin 64, rowSlice (640+i.val) := joinChunks (P := rowSlice) (start := 640) (a := 32) (b := 32) rowSlice_640_672 rowSlice_672_704

private theorem rowSlice_704_712 : ∀ i : Fin 8, rowSlice (704+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_712_720 : ∀ i : Fin 8, rowSlice (712+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_704_720 : ∀ i : Fin 16, rowSlice (704+i.val) := joinChunks (P := rowSlice) (start := 704) (a := 8) (b := 8) rowSlice_704_712 rowSlice_712_720

private theorem rowSlice_720_728 : ∀ i : Fin 8, rowSlice (720+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_728_736 : ∀ i : Fin 8, rowSlice (728+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_720_736 : ∀ i : Fin 16, rowSlice (720+i.val) := joinChunks (P := rowSlice) (start := 720) (a := 8) (b := 8) rowSlice_720_728 rowSlice_728_736

private theorem rowSlice_704_736 : ∀ i : Fin 32, rowSlice (704+i.val) := joinChunks (P := rowSlice) (start := 704) (a := 16) (b := 16) rowSlice_704_720 rowSlice_720_736

private theorem rowSlice_736_744 : ∀ i : Fin 8, rowSlice (736+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_744_752 : ∀ i : Fin 8, rowSlice (744+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_736_752 : ∀ i : Fin 16, rowSlice (736+i.val) := joinChunks (P := rowSlice) (start := 736) (a := 8) (b := 8) rowSlice_736_744 rowSlice_744_752

private theorem rowSlice_752_760 : ∀ i : Fin 8, rowSlice (752+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_760_768 : ∀ i : Fin 8, rowSlice (760+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_752_768 : ∀ i : Fin 16, rowSlice (752+i.val) := joinChunks (P := rowSlice) (start := 752) (a := 8) (b := 8) rowSlice_752_760 rowSlice_760_768

private theorem rowSlice_736_768 : ∀ i : Fin 32, rowSlice (736+i.val) := joinChunks (P := rowSlice) (start := 736) (a := 16) (b := 16) rowSlice_736_752 rowSlice_752_768

private theorem rowSlice_704_768 : ∀ i : Fin 64, rowSlice (704+i.val) := joinChunks (P := rowSlice) (start := 704) (a := 32) (b := 32) rowSlice_704_736 rowSlice_736_768

private theorem rowSlice_640_768 : ∀ i : Fin 128, rowSlice (640+i.val) := joinChunks (P := rowSlice) (start := 640) (a := 64) (b := 64) rowSlice_640_704 rowSlice_704_768

private theorem rowSlice_512_768 : ∀ i : Fin 256, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 128) (b := 128) rowSlice_512_640 rowSlice_640_768

private theorem rowSlice_768_776 : ∀ i : Fin 8, rowSlice (768+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_776_784 : ∀ i : Fin 8, rowSlice (776+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_768_784 : ∀ i : Fin 16, rowSlice (768+i.val) := joinChunks (P := rowSlice) (start := 768) (a := 8) (b := 8) rowSlice_768_776 rowSlice_776_784

private theorem rowSlice_784_792 : ∀ i : Fin 8, rowSlice (784+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_792_800 : ∀ i : Fin 8, rowSlice (792+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_784_800 : ∀ i : Fin 16, rowSlice (784+i.val) := joinChunks (P := rowSlice) (start := 784) (a := 8) (b := 8) rowSlice_784_792 rowSlice_792_800

private theorem rowSlice_768_800 : ∀ i : Fin 32, rowSlice (768+i.val) := joinChunks (P := rowSlice) (start := 768) (a := 16) (b := 16) rowSlice_768_784 rowSlice_784_800

private theorem rowSlice_800_808 : ∀ i : Fin 8, rowSlice (800+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_808_816 : ∀ i : Fin 8, rowSlice (808+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_800_816 : ∀ i : Fin 16, rowSlice (800+i.val) := joinChunks (P := rowSlice) (start := 800) (a := 8) (b := 8) rowSlice_800_808 rowSlice_808_816

private theorem rowSlice_816_824 : ∀ i : Fin 8, rowSlice (816+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_824_832 : ∀ i : Fin 8, rowSlice (824+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_816_832 : ∀ i : Fin 16, rowSlice (816+i.val) := joinChunks (P := rowSlice) (start := 816) (a := 8) (b := 8) rowSlice_816_824 rowSlice_824_832

private theorem rowSlice_800_832 : ∀ i : Fin 32, rowSlice (800+i.val) := joinChunks (P := rowSlice) (start := 800) (a := 16) (b := 16) rowSlice_800_816 rowSlice_816_832

private theorem rowSlice_768_832 : ∀ i : Fin 64, rowSlice (768+i.val) := joinChunks (P := rowSlice) (start := 768) (a := 32) (b := 32) rowSlice_768_800 rowSlice_800_832

private theorem rowSlice_832_840 : ∀ i : Fin 8, rowSlice (832+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_840_848 : ∀ i : Fin 8, rowSlice (840+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_832_848 : ∀ i : Fin 16, rowSlice (832+i.val) := joinChunks (P := rowSlice) (start := 832) (a := 8) (b := 8) rowSlice_832_840 rowSlice_840_848

private theorem rowSlice_848_856 : ∀ i : Fin 8, rowSlice (848+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_856_864 : ∀ i : Fin 8, rowSlice (856+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_848_864 : ∀ i : Fin 16, rowSlice (848+i.val) := joinChunks (P := rowSlice) (start := 848) (a := 8) (b := 8) rowSlice_848_856 rowSlice_856_864

private theorem rowSlice_832_864 : ∀ i : Fin 32, rowSlice (832+i.val) := joinChunks (P := rowSlice) (start := 832) (a := 16) (b := 16) rowSlice_832_848 rowSlice_848_864

private theorem rowSlice_864_872 : ∀ i : Fin 8, rowSlice (864+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_872_880 : ∀ i : Fin 8, rowSlice (872+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_864_880 : ∀ i : Fin 16, rowSlice (864+i.val) := joinChunks (P := rowSlice) (start := 864) (a := 8) (b := 8) rowSlice_864_872 rowSlice_872_880

private theorem rowSlice_880_888 : ∀ i : Fin 8, rowSlice (880+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_888_896 : ∀ i : Fin 8, rowSlice (888+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_880_896 : ∀ i : Fin 16, rowSlice (880+i.val) := joinChunks (P := rowSlice) (start := 880) (a := 8) (b := 8) rowSlice_880_888 rowSlice_888_896

private theorem rowSlice_864_896 : ∀ i : Fin 32, rowSlice (864+i.val) := joinChunks (P := rowSlice) (start := 864) (a := 16) (b := 16) rowSlice_864_880 rowSlice_880_896

private theorem rowSlice_832_896 : ∀ i : Fin 64, rowSlice (832+i.val) := joinChunks (P := rowSlice) (start := 832) (a := 32) (b := 32) rowSlice_832_864 rowSlice_864_896

private theorem rowSlice_768_896 : ∀ i : Fin 128, rowSlice (768+i.val) := joinChunks (P := rowSlice) (start := 768) (a := 64) (b := 64) rowSlice_768_832 rowSlice_832_896

private theorem rowSlice_896_904 : ∀ i : Fin 8, rowSlice (896+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_904_912 : ∀ i : Fin 8, rowSlice (904+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_896_912 : ∀ i : Fin 16, rowSlice (896+i.val) := joinChunks (P := rowSlice) (start := 896) (a := 8) (b := 8) rowSlice_896_904 rowSlice_904_912

private theorem rowSlice_912_920 : ∀ i : Fin 8, rowSlice (912+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_920_928 : ∀ i : Fin 8, rowSlice (920+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_912_928 : ∀ i : Fin 16, rowSlice (912+i.val) := joinChunks (P := rowSlice) (start := 912) (a := 8) (b := 8) rowSlice_912_920 rowSlice_920_928

private theorem rowSlice_896_928 : ∀ i : Fin 32, rowSlice (896+i.val) := joinChunks (P := rowSlice) (start := 896) (a := 16) (b := 16) rowSlice_896_912 rowSlice_912_928

private theorem rowSlice_928_936 : ∀ i : Fin 8, rowSlice (928+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_936_944 : ∀ i : Fin 8, rowSlice (936+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_928_944 : ∀ i : Fin 16, rowSlice (928+i.val) := joinChunks (P := rowSlice) (start := 928) (a := 8) (b := 8) rowSlice_928_936 rowSlice_936_944

private theorem rowSlice_944_952 : ∀ i : Fin 8, rowSlice (944+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_952_960 : ∀ i : Fin 8, rowSlice (952+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_944_960 : ∀ i : Fin 16, rowSlice (944+i.val) := joinChunks (P := rowSlice) (start := 944) (a := 8) (b := 8) rowSlice_944_952 rowSlice_952_960

private theorem rowSlice_928_960 : ∀ i : Fin 32, rowSlice (928+i.val) := joinChunks (P := rowSlice) (start := 928) (a := 16) (b := 16) rowSlice_928_944 rowSlice_944_960

private theorem rowSlice_896_960 : ∀ i : Fin 64, rowSlice (896+i.val) := joinChunks (P := rowSlice) (start := 896) (a := 32) (b := 32) rowSlice_896_928 rowSlice_928_960

private theorem rowSlice_960_968 : ∀ i : Fin 8, rowSlice (960+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_968_976 : ∀ i : Fin 8, rowSlice (968+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_960_976 : ∀ i : Fin 16, rowSlice (960+i.val) := joinChunks (P := rowSlice) (start := 960) (a := 8) (b := 8) rowSlice_960_968 rowSlice_968_976

private theorem rowSlice_976_984 : ∀ i : Fin 8, rowSlice (976+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_984_992 : ∀ i : Fin 8, rowSlice (984+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_976_992 : ∀ i : Fin 16, rowSlice (976+i.val) := joinChunks (P := rowSlice) (start := 976) (a := 8) (b := 8) rowSlice_976_984 rowSlice_984_992

private theorem rowSlice_960_992 : ∀ i : Fin 32, rowSlice (960+i.val) := joinChunks (P := rowSlice) (start := 960) (a := 16) (b := 16) rowSlice_960_976 rowSlice_976_992

private theorem rowSlice_992_1000 : ∀ i : Fin 8, rowSlice (992+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_1000_1008 : ∀ i : Fin 8, rowSlice (1000+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_992_1008 : ∀ i : Fin 16, rowSlice (992+i.val) := joinChunks (P := rowSlice) (start := 992) (a := 8) (b := 8) rowSlice_992_1000 rowSlice_1000_1008

private theorem rowSlice_1008_1016 : ∀ i : Fin 8, rowSlice (1008+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_1016_1024 : ∀ i : Fin 8, rowSlice (1016+i.val) := by unfold rowSlice; decide +kernel

private theorem rowSlice_1008_1024 : ∀ i : Fin 16, rowSlice (1008+i.val) := joinChunks (P := rowSlice) (start := 1008) (a := 8) (b := 8) rowSlice_1008_1016 rowSlice_1016_1024

private theorem rowSlice_992_1024 : ∀ i : Fin 32, rowSlice (992+i.val) := joinChunks (P := rowSlice) (start := 992) (a := 16) (b := 16) rowSlice_992_1008 rowSlice_1008_1024

private theorem rowSlice_960_1024 : ∀ i : Fin 64, rowSlice (960+i.val) := joinChunks (P := rowSlice) (start := 960) (a := 32) (b := 32) rowSlice_960_992 rowSlice_992_1024

private theorem rowSlice_896_1024 : ∀ i : Fin 128, rowSlice (896+i.val) := joinChunks (P := rowSlice) (start := 896) (a := 64) (b := 64) rowSlice_896_960 rowSlice_960_1024

private theorem rowSlice_768_1024 : ∀ i : Fin 256, rowSlice (768+i.val) := joinChunks (P := rowSlice) (start := 768) (a := 128) (b := 128) rowSlice_768_896 rowSlice_896_1024

private theorem rowSlice_512_1024 : ∀ i : Fin 512, rowSlice (512+i.val) := joinChunks (P := rowSlice) (start := 512) (a := 256) (b := 256) rowSlice_512_768 rowSlice_768_1024

private theorem rowSlice_0_1024 : ∀ i : Fin 1024, rowSlice (0+i.val) := joinChunks (P := rowSlice) (start := 0) (a := 512) (b := 512) rowSlice_0_512 rowSlice_512_1024

theorem slice (c : Core) : row (label c) = BitVec.ofNat 32 (packed.toNat >>> (32*c.val)) := by
  simpa [rowSlice,Fin.ofNat,Nat.mod_eq_of_lt c.isLt] using rowSlice_0_1024 c

def signal {k : Nat} (m : Nat) : Finset (Fin k) :=
  Finset.univ.filter fun i => m.testBit i.val

def code (a : Label) := signal (k := 8) (message a).val

private def separatedRow (i : Nat) : Prop := ∀ j : Fin 45, Fin.ofNat 45 i ≠ j → ∃ z : Neighbours, (row (separated (Fin.ofNat 45 i))).getLsbD z.val = true ∧ (row (separated j)).getLsbD z.val = false

private theorem separatedRow_0_2 : ∀ i : Fin 2, separatedRow (0+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_2_3 : ∀ i : Fin 1, separatedRow (2+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_3_5 : ∀ i : Fin 2, separatedRow (3+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_2_5 : ∀ i : Fin 3, separatedRow (2+i.val) := joinChunks (P := separatedRow) (start := 2) (a := 1) (b := 2) separatedRow_2_3 separatedRow_3_5

private theorem separatedRow_0_5 : ∀ i : Fin 5, separatedRow (0+i.val) := joinChunks (P := separatedRow) (start := 0) (a := 2) (b := 3) separatedRow_0_2 separatedRow_2_5

private theorem separatedRow_5_6 : ∀ i : Fin 1, separatedRow (5+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_6_8 : ∀ i : Fin 2, separatedRow (6+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_5_8 : ∀ i : Fin 3, separatedRow (5+i.val) := joinChunks (P := separatedRow) (start := 5) (a := 1) (b := 2) separatedRow_5_6 separatedRow_6_8

private theorem separatedRow_8_9 : ∀ i : Fin 1, separatedRow (8+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_9_11 : ∀ i : Fin 2, separatedRow (9+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_8_11 : ∀ i : Fin 3, separatedRow (8+i.val) := joinChunks (P := separatedRow) (start := 8) (a := 1) (b := 2) separatedRow_8_9 separatedRow_9_11

private theorem separatedRow_5_11 : ∀ i : Fin 6, separatedRow (5+i.val) := joinChunks (P := separatedRow) (start := 5) (a := 3) (b := 3) separatedRow_5_8 separatedRow_8_11

private theorem separatedRow_0_11 : ∀ i : Fin 11, separatedRow (0+i.val) := joinChunks (P := separatedRow) (start := 0) (a := 5) (b := 6) separatedRow_0_5 separatedRow_5_11

private theorem separatedRow_11_13 : ∀ i : Fin 2, separatedRow (11+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_13_14 : ∀ i : Fin 1, separatedRow (13+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_14_16 : ∀ i : Fin 2, separatedRow (14+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_13_16 : ∀ i : Fin 3, separatedRow (13+i.val) := joinChunks (P := separatedRow) (start := 13) (a := 1) (b := 2) separatedRow_13_14 separatedRow_14_16

private theorem separatedRow_11_16 : ∀ i : Fin 5, separatedRow (11+i.val) := joinChunks (P := separatedRow) (start := 11) (a := 2) (b := 3) separatedRow_11_13 separatedRow_13_16

private theorem separatedRow_16_17 : ∀ i : Fin 1, separatedRow (16+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_17_19 : ∀ i : Fin 2, separatedRow (17+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_16_19 : ∀ i : Fin 3, separatedRow (16+i.val) := joinChunks (P := separatedRow) (start := 16) (a := 1) (b := 2) separatedRow_16_17 separatedRow_17_19

private theorem separatedRow_19_20 : ∀ i : Fin 1, separatedRow (19+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_20_22 : ∀ i : Fin 2, separatedRow (20+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_19_22 : ∀ i : Fin 3, separatedRow (19+i.val) := joinChunks (P := separatedRow) (start := 19) (a := 1) (b := 2) separatedRow_19_20 separatedRow_20_22

private theorem separatedRow_16_22 : ∀ i : Fin 6, separatedRow (16+i.val) := joinChunks (P := separatedRow) (start := 16) (a := 3) (b := 3) separatedRow_16_19 separatedRow_19_22

private theorem separatedRow_11_22 : ∀ i : Fin 11, separatedRow (11+i.val) := joinChunks (P := separatedRow) (start := 11) (a := 5) (b := 6) separatedRow_11_16 separatedRow_16_22

private theorem separatedRow_0_22 : ∀ i : Fin 22, separatedRow (0+i.val) := joinChunks (P := separatedRow) (start := 0) (a := 11) (b := 11) separatedRow_0_11 separatedRow_11_22

private theorem separatedRow_22_24 : ∀ i : Fin 2, separatedRow (22+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_24_25 : ∀ i : Fin 1, separatedRow (24+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_25_27 : ∀ i : Fin 2, separatedRow (25+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_24_27 : ∀ i : Fin 3, separatedRow (24+i.val) := joinChunks (P := separatedRow) (start := 24) (a := 1) (b := 2) separatedRow_24_25 separatedRow_25_27

private theorem separatedRow_22_27 : ∀ i : Fin 5, separatedRow (22+i.val) := joinChunks (P := separatedRow) (start := 22) (a := 2) (b := 3) separatedRow_22_24 separatedRow_24_27

private theorem separatedRow_27_28 : ∀ i : Fin 1, separatedRow (27+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_28_30 : ∀ i : Fin 2, separatedRow (28+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_27_30 : ∀ i : Fin 3, separatedRow (27+i.val) := joinChunks (P := separatedRow) (start := 27) (a := 1) (b := 2) separatedRow_27_28 separatedRow_28_30

private theorem separatedRow_30_31 : ∀ i : Fin 1, separatedRow (30+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_31_33 : ∀ i : Fin 2, separatedRow (31+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_30_33 : ∀ i : Fin 3, separatedRow (30+i.val) := joinChunks (P := separatedRow) (start := 30) (a := 1) (b := 2) separatedRow_30_31 separatedRow_31_33

private theorem separatedRow_27_33 : ∀ i : Fin 6, separatedRow (27+i.val) := joinChunks (P := separatedRow) (start := 27) (a := 3) (b := 3) separatedRow_27_30 separatedRow_30_33

private theorem separatedRow_22_33 : ∀ i : Fin 11, separatedRow (22+i.val) := joinChunks (P := separatedRow) (start := 22) (a := 5) (b := 6) separatedRow_22_27 separatedRow_27_33

private theorem separatedRow_33_34 : ∀ i : Fin 1, separatedRow (33+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_34_36 : ∀ i : Fin 2, separatedRow (34+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_33_36 : ∀ i : Fin 3, separatedRow (33+i.val) := joinChunks (P := separatedRow) (start := 33) (a := 1) (b := 2) separatedRow_33_34 separatedRow_34_36

private theorem separatedRow_36_37 : ∀ i : Fin 1, separatedRow (36+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_37_39 : ∀ i : Fin 2, separatedRow (37+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_36_39 : ∀ i : Fin 3, separatedRow (36+i.val) := joinChunks (P := separatedRow) (start := 36) (a := 1) (b := 2) separatedRow_36_37 separatedRow_37_39

private theorem separatedRow_33_39 : ∀ i : Fin 6, separatedRow (33+i.val) := joinChunks (P := separatedRow) (start := 33) (a := 3) (b := 3) separatedRow_33_36 separatedRow_36_39

private theorem separatedRow_39_40 : ∀ i : Fin 1, separatedRow (39+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_40_42 : ∀ i : Fin 2, separatedRow (40+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_39_42 : ∀ i : Fin 3, separatedRow (39+i.val) := joinChunks (P := separatedRow) (start := 39) (a := 1) (b := 2) separatedRow_39_40 separatedRow_40_42

private theorem separatedRow_42_43 : ∀ i : Fin 1, separatedRow (42+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_43_45 : ∀ i : Fin 2, separatedRow (43+i.val) := by unfold separatedRow; decide +kernel

private theorem separatedRow_42_45 : ∀ i : Fin 3, separatedRow (42+i.val) := joinChunks (P := separatedRow) (start := 42) (a := 1) (b := 2) separatedRow_42_43 separatedRow_43_45

private theorem separatedRow_39_45 : ∀ i : Fin 6, separatedRow (39+i.val) := joinChunks (P := separatedRow) (start := 39) (a := 3) (b := 3) separatedRow_39_42 separatedRow_42_45

private theorem separatedRow_33_45 : ∀ i : Fin 12, separatedRow (33+i.val) := joinChunks (P := separatedRow) (start := 33) (a := 6) (b := 6) separatedRow_33_39 separatedRow_39_45

private theorem separatedRow_22_45 : ∀ i : Fin 23, separatedRow (22+i.val) := joinChunks (P := separatedRow) (start := 22) (a := 11) (b := 12) separatedRow_22_33 separatedRow_33_45

private theorem separatedRow_0_45 : ∀ i : Fin 45, separatedRow (0+i.val) := joinChunks (P := separatedRow) (start := 0) (a := 22) (b := 23) separatedRow_0_22 separatedRow_22_45

theorem separates (i j : Fin 45) (h : i ≠ j) : ∃ z : Neighbours,
    (row (separated i)).getLsbD z.val = true ∧ (row (separated j)).getLsbD z.val = false := by
  have t := separatedRow_0_45 i
  simpa [Fin.ofNat,Nat.mod_eq_of_lt i.isLt] using t j (by simpa [Fin.ofNat,Nat.mod_eq_of_lt i.isLt] using h)

private def codeTest (i : Nat) : Prop := ∀ j : Label, code (Fin.ofNat 83 i) ⊆ code j → row (Fin.ofNat 83 i) &&& row j = row (Fin.ofNat 83 i)

private theorem codeTest_0_1 : ∀ i : Fin 1, codeTest (0+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_1_2 : ∀ i : Fin 1, codeTest (1+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_0_2 : ∀ i : Fin 2, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 1) (b := 1) codeTest_0_1 codeTest_1_2

private theorem codeTest_2_3 : ∀ i : Fin 1, codeTest (2+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_3_4 : ∀ i : Fin 1, codeTest (3+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_4_5 : ∀ i : Fin 1, codeTest (4+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_3_5 : ∀ i : Fin 2, codeTest (3+i.val) := joinChunks (P := codeTest) (start := 3) (a := 1) (b := 1) codeTest_3_4 codeTest_4_5

private theorem codeTest_2_5 : ∀ i : Fin 3, codeTest (2+i.val) := joinChunks (P := codeTest) (start := 2) (a := 1) (b := 2) codeTest_2_3 codeTest_3_5

private theorem codeTest_0_5 : ∀ i : Fin 5, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 2) (b := 3) codeTest_0_2 codeTest_2_5

private theorem codeTest_5_6 : ∀ i : Fin 1, codeTest (5+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_6_7 : ∀ i : Fin 1, codeTest (6+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_5_7 : ∀ i : Fin 2, codeTest (5+i.val) := joinChunks (P := codeTest) (start := 5) (a := 1) (b := 1) codeTest_5_6 codeTest_6_7

private theorem codeTest_7_8 : ∀ i : Fin 1, codeTest (7+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_8_9 : ∀ i : Fin 1, codeTest (8+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_9_10 : ∀ i : Fin 1, codeTest (9+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_8_10 : ∀ i : Fin 2, codeTest (8+i.val) := joinChunks (P := codeTest) (start := 8) (a := 1) (b := 1) codeTest_8_9 codeTest_9_10

private theorem codeTest_7_10 : ∀ i : Fin 3, codeTest (7+i.val) := joinChunks (P := codeTest) (start := 7) (a := 1) (b := 2) codeTest_7_8 codeTest_8_10

private theorem codeTest_5_10 : ∀ i : Fin 5, codeTest (5+i.val) := joinChunks (P := codeTest) (start := 5) (a := 2) (b := 3) codeTest_5_7 codeTest_7_10

private theorem codeTest_0_10 : ∀ i : Fin 10, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 5) (b := 5) codeTest_0_5 codeTest_5_10

private theorem codeTest_10_11 : ∀ i : Fin 1, codeTest (10+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_11_12 : ∀ i : Fin 1, codeTest (11+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_10_12 : ∀ i : Fin 2, codeTest (10+i.val) := joinChunks (P := codeTest) (start := 10) (a := 1) (b := 1) codeTest_10_11 codeTest_11_12

private theorem codeTest_12_13 : ∀ i : Fin 1, codeTest (12+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_13_14 : ∀ i : Fin 1, codeTest (13+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_14_15 : ∀ i : Fin 1, codeTest (14+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_13_15 : ∀ i : Fin 2, codeTest (13+i.val) := joinChunks (P := codeTest) (start := 13) (a := 1) (b := 1) codeTest_13_14 codeTest_14_15

private theorem codeTest_12_15 : ∀ i : Fin 3, codeTest (12+i.val) := joinChunks (P := codeTest) (start := 12) (a := 1) (b := 2) codeTest_12_13 codeTest_13_15

private theorem codeTest_10_15 : ∀ i : Fin 5, codeTest (10+i.val) := joinChunks (P := codeTest) (start := 10) (a := 2) (b := 3) codeTest_10_12 codeTest_12_15

private theorem codeTest_15_16 : ∀ i : Fin 1, codeTest (15+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_16_17 : ∀ i : Fin 1, codeTest (16+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_15_17 : ∀ i : Fin 2, codeTest (15+i.val) := joinChunks (P := codeTest) (start := 15) (a := 1) (b := 1) codeTest_15_16 codeTest_16_17

private theorem codeTest_17_18 : ∀ i : Fin 1, codeTest (17+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_18_19 : ∀ i : Fin 1, codeTest (18+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_19_20 : ∀ i : Fin 1, codeTest (19+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_18_20 : ∀ i : Fin 2, codeTest (18+i.val) := joinChunks (P := codeTest) (start := 18) (a := 1) (b := 1) codeTest_18_19 codeTest_19_20

private theorem codeTest_17_20 : ∀ i : Fin 3, codeTest (17+i.val) := joinChunks (P := codeTest) (start := 17) (a := 1) (b := 2) codeTest_17_18 codeTest_18_20

private theorem codeTest_15_20 : ∀ i : Fin 5, codeTest (15+i.val) := joinChunks (P := codeTest) (start := 15) (a := 2) (b := 3) codeTest_15_17 codeTest_17_20

private theorem codeTest_10_20 : ∀ i : Fin 10, codeTest (10+i.val) := joinChunks (P := codeTest) (start := 10) (a := 5) (b := 5) codeTest_10_15 codeTest_15_20

private theorem codeTest_0_20 : ∀ i : Fin 20, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 10) (b := 10) codeTest_0_10 codeTest_10_20

private theorem codeTest_20_21 : ∀ i : Fin 1, codeTest (20+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_21_22 : ∀ i : Fin 1, codeTest (21+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_20_22 : ∀ i : Fin 2, codeTest (20+i.val) := joinChunks (P := codeTest) (start := 20) (a := 1) (b := 1) codeTest_20_21 codeTest_21_22

private theorem codeTest_22_23 : ∀ i : Fin 1, codeTest (22+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_23_24 : ∀ i : Fin 1, codeTest (23+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_24_25 : ∀ i : Fin 1, codeTest (24+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_23_25 : ∀ i : Fin 2, codeTest (23+i.val) := joinChunks (P := codeTest) (start := 23) (a := 1) (b := 1) codeTest_23_24 codeTest_24_25

private theorem codeTest_22_25 : ∀ i : Fin 3, codeTest (22+i.val) := joinChunks (P := codeTest) (start := 22) (a := 1) (b := 2) codeTest_22_23 codeTest_23_25

private theorem codeTest_20_25 : ∀ i : Fin 5, codeTest (20+i.val) := joinChunks (P := codeTest) (start := 20) (a := 2) (b := 3) codeTest_20_22 codeTest_22_25

private theorem codeTest_25_26 : ∀ i : Fin 1, codeTest (25+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_26_27 : ∀ i : Fin 1, codeTest (26+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_25_27 : ∀ i : Fin 2, codeTest (25+i.val) := joinChunks (P := codeTest) (start := 25) (a := 1) (b := 1) codeTest_25_26 codeTest_26_27

private theorem codeTest_27_28 : ∀ i : Fin 1, codeTest (27+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_28_29 : ∀ i : Fin 1, codeTest (28+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_29_30 : ∀ i : Fin 1, codeTest (29+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_28_30 : ∀ i : Fin 2, codeTest (28+i.val) := joinChunks (P := codeTest) (start := 28) (a := 1) (b := 1) codeTest_28_29 codeTest_29_30

private theorem codeTest_27_30 : ∀ i : Fin 3, codeTest (27+i.val) := joinChunks (P := codeTest) (start := 27) (a := 1) (b := 2) codeTest_27_28 codeTest_28_30

private theorem codeTest_25_30 : ∀ i : Fin 5, codeTest (25+i.val) := joinChunks (P := codeTest) (start := 25) (a := 2) (b := 3) codeTest_25_27 codeTest_27_30

private theorem codeTest_20_30 : ∀ i : Fin 10, codeTest (20+i.val) := joinChunks (P := codeTest) (start := 20) (a := 5) (b := 5) codeTest_20_25 codeTest_25_30

private theorem codeTest_30_31 : ∀ i : Fin 1, codeTest (30+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_31_32 : ∀ i : Fin 1, codeTest (31+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_30_32 : ∀ i : Fin 2, codeTest (30+i.val) := joinChunks (P := codeTest) (start := 30) (a := 1) (b := 1) codeTest_30_31 codeTest_31_32

private theorem codeTest_32_33 : ∀ i : Fin 1, codeTest (32+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_33_34 : ∀ i : Fin 1, codeTest (33+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_34_35 : ∀ i : Fin 1, codeTest (34+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_33_35 : ∀ i : Fin 2, codeTest (33+i.val) := joinChunks (P := codeTest) (start := 33) (a := 1) (b := 1) codeTest_33_34 codeTest_34_35

private theorem codeTest_32_35 : ∀ i : Fin 3, codeTest (32+i.val) := joinChunks (P := codeTest) (start := 32) (a := 1) (b := 2) codeTest_32_33 codeTest_33_35

private theorem codeTest_30_35 : ∀ i : Fin 5, codeTest (30+i.val) := joinChunks (P := codeTest) (start := 30) (a := 2) (b := 3) codeTest_30_32 codeTest_32_35

private theorem codeTest_35_36 : ∀ i : Fin 1, codeTest (35+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_36_37 : ∀ i : Fin 1, codeTest (36+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_37_38 : ∀ i : Fin 1, codeTest (37+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_36_38 : ∀ i : Fin 2, codeTest (36+i.val) := joinChunks (P := codeTest) (start := 36) (a := 1) (b := 1) codeTest_36_37 codeTest_37_38

private theorem codeTest_35_38 : ∀ i : Fin 3, codeTest (35+i.val) := joinChunks (P := codeTest) (start := 35) (a := 1) (b := 2) codeTest_35_36 codeTest_36_38

private theorem codeTest_38_39 : ∀ i : Fin 1, codeTest (38+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_39_40 : ∀ i : Fin 1, codeTest (39+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_40_41 : ∀ i : Fin 1, codeTest (40+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_39_41 : ∀ i : Fin 2, codeTest (39+i.val) := joinChunks (P := codeTest) (start := 39) (a := 1) (b := 1) codeTest_39_40 codeTest_40_41

private theorem codeTest_38_41 : ∀ i : Fin 3, codeTest (38+i.val) := joinChunks (P := codeTest) (start := 38) (a := 1) (b := 2) codeTest_38_39 codeTest_39_41

private theorem codeTest_35_41 : ∀ i : Fin 6, codeTest (35+i.val) := joinChunks (P := codeTest) (start := 35) (a := 3) (b := 3) codeTest_35_38 codeTest_38_41

private theorem codeTest_30_41 : ∀ i : Fin 11, codeTest (30+i.val) := joinChunks (P := codeTest) (start := 30) (a := 5) (b := 6) codeTest_30_35 codeTest_35_41

private theorem codeTest_20_41 : ∀ i : Fin 21, codeTest (20+i.val) := joinChunks (P := codeTest) (start := 20) (a := 10) (b := 11) codeTest_20_30 codeTest_30_41

private theorem codeTest_0_41 : ∀ i : Fin 41, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 20) (b := 21) codeTest_0_20 codeTest_20_41

private theorem codeTest_41_42 : ∀ i : Fin 1, codeTest (41+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_42_43 : ∀ i : Fin 1, codeTest (42+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_41_43 : ∀ i : Fin 2, codeTest (41+i.val) := joinChunks (P := codeTest) (start := 41) (a := 1) (b := 1) codeTest_41_42 codeTest_42_43

private theorem codeTest_43_44 : ∀ i : Fin 1, codeTest (43+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_44_45 : ∀ i : Fin 1, codeTest (44+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_45_46 : ∀ i : Fin 1, codeTest (45+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_44_46 : ∀ i : Fin 2, codeTest (44+i.val) := joinChunks (P := codeTest) (start := 44) (a := 1) (b := 1) codeTest_44_45 codeTest_45_46

private theorem codeTest_43_46 : ∀ i : Fin 3, codeTest (43+i.val) := joinChunks (P := codeTest) (start := 43) (a := 1) (b := 2) codeTest_43_44 codeTest_44_46

private theorem codeTest_41_46 : ∀ i : Fin 5, codeTest (41+i.val) := joinChunks (P := codeTest) (start := 41) (a := 2) (b := 3) codeTest_41_43 codeTest_43_46

private theorem codeTest_46_47 : ∀ i : Fin 1, codeTest (46+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_47_48 : ∀ i : Fin 1, codeTest (47+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_46_48 : ∀ i : Fin 2, codeTest (46+i.val) := joinChunks (P := codeTest) (start := 46) (a := 1) (b := 1) codeTest_46_47 codeTest_47_48

private theorem codeTest_48_49 : ∀ i : Fin 1, codeTest (48+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_49_50 : ∀ i : Fin 1, codeTest (49+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_50_51 : ∀ i : Fin 1, codeTest (50+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_49_51 : ∀ i : Fin 2, codeTest (49+i.val) := joinChunks (P := codeTest) (start := 49) (a := 1) (b := 1) codeTest_49_50 codeTest_50_51

private theorem codeTest_48_51 : ∀ i : Fin 3, codeTest (48+i.val) := joinChunks (P := codeTest) (start := 48) (a := 1) (b := 2) codeTest_48_49 codeTest_49_51

private theorem codeTest_46_51 : ∀ i : Fin 5, codeTest (46+i.val) := joinChunks (P := codeTest) (start := 46) (a := 2) (b := 3) codeTest_46_48 codeTest_48_51

private theorem codeTest_41_51 : ∀ i : Fin 10, codeTest (41+i.val) := joinChunks (P := codeTest) (start := 41) (a := 5) (b := 5) codeTest_41_46 codeTest_46_51

private theorem codeTest_51_52 : ∀ i : Fin 1, codeTest (51+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_52_53 : ∀ i : Fin 1, codeTest (52+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_51_53 : ∀ i : Fin 2, codeTest (51+i.val) := joinChunks (P := codeTest) (start := 51) (a := 1) (b := 1) codeTest_51_52 codeTest_52_53

private theorem codeTest_53_54 : ∀ i : Fin 1, codeTest (53+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_54_55 : ∀ i : Fin 1, codeTest (54+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_55_56 : ∀ i : Fin 1, codeTest (55+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_54_56 : ∀ i : Fin 2, codeTest (54+i.val) := joinChunks (P := codeTest) (start := 54) (a := 1) (b := 1) codeTest_54_55 codeTest_55_56

private theorem codeTest_53_56 : ∀ i : Fin 3, codeTest (53+i.val) := joinChunks (P := codeTest) (start := 53) (a := 1) (b := 2) codeTest_53_54 codeTest_54_56

private theorem codeTest_51_56 : ∀ i : Fin 5, codeTest (51+i.val) := joinChunks (P := codeTest) (start := 51) (a := 2) (b := 3) codeTest_51_53 codeTest_53_56

private theorem codeTest_56_57 : ∀ i : Fin 1, codeTest (56+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_57_58 : ∀ i : Fin 1, codeTest (57+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_58_59 : ∀ i : Fin 1, codeTest (58+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_57_59 : ∀ i : Fin 2, codeTest (57+i.val) := joinChunks (P := codeTest) (start := 57) (a := 1) (b := 1) codeTest_57_58 codeTest_58_59

private theorem codeTest_56_59 : ∀ i : Fin 3, codeTest (56+i.val) := joinChunks (P := codeTest) (start := 56) (a := 1) (b := 2) codeTest_56_57 codeTest_57_59

private theorem codeTest_59_60 : ∀ i : Fin 1, codeTest (59+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_60_61 : ∀ i : Fin 1, codeTest (60+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_61_62 : ∀ i : Fin 1, codeTest (61+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_60_62 : ∀ i : Fin 2, codeTest (60+i.val) := joinChunks (P := codeTest) (start := 60) (a := 1) (b := 1) codeTest_60_61 codeTest_61_62

private theorem codeTest_59_62 : ∀ i : Fin 3, codeTest (59+i.val) := joinChunks (P := codeTest) (start := 59) (a := 1) (b := 2) codeTest_59_60 codeTest_60_62

private theorem codeTest_56_62 : ∀ i : Fin 6, codeTest (56+i.val) := joinChunks (P := codeTest) (start := 56) (a := 3) (b := 3) codeTest_56_59 codeTest_59_62

private theorem codeTest_51_62 : ∀ i : Fin 11, codeTest (51+i.val) := joinChunks (P := codeTest) (start := 51) (a := 5) (b := 6) codeTest_51_56 codeTest_56_62

private theorem codeTest_41_62 : ∀ i : Fin 21, codeTest (41+i.val) := joinChunks (P := codeTest) (start := 41) (a := 10) (b := 11) codeTest_41_51 codeTest_51_62

private theorem codeTest_62_63 : ∀ i : Fin 1, codeTest (62+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_63_64 : ∀ i : Fin 1, codeTest (63+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_62_64 : ∀ i : Fin 2, codeTest (62+i.val) := joinChunks (P := codeTest) (start := 62) (a := 1) (b := 1) codeTest_62_63 codeTest_63_64

private theorem codeTest_64_65 : ∀ i : Fin 1, codeTest (64+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_65_66 : ∀ i : Fin 1, codeTest (65+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_66_67 : ∀ i : Fin 1, codeTest (66+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_65_67 : ∀ i : Fin 2, codeTest (65+i.val) := joinChunks (P := codeTest) (start := 65) (a := 1) (b := 1) codeTest_65_66 codeTest_66_67

private theorem codeTest_64_67 : ∀ i : Fin 3, codeTest (64+i.val) := joinChunks (P := codeTest) (start := 64) (a := 1) (b := 2) codeTest_64_65 codeTest_65_67

private theorem codeTest_62_67 : ∀ i : Fin 5, codeTest (62+i.val) := joinChunks (P := codeTest) (start := 62) (a := 2) (b := 3) codeTest_62_64 codeTest_64_67

private theorem codeTest_67_68 : ∀ i : Fin 1, codeTest (67+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_68_69 : ∀ i : Fin 1, codeTest (68+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_67_69 : ∀ i : Fin 2, codeTest (67+i.val) := joinChunks (P := codeTest) (start := 67) (a := 1) (b := 1) codeTest_67_68 codeTest_68_69

private theorem codeTest_69_70 : ∀ i : Fin 1, codeTest (69+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_70_71 : ∀ i : Fin 1, codeTest (70+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_71_72 : ∀ i : Fin 1, codeTest (71+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_70_72 : ∀ i : Fin 2, codeTest (70+i.val) := joinChunks (P := codeTest) (start := 70) (a := 1) (b := 1) codeTest_70_71 codeTest_71_72

private theorem codeTest_69_72 : ∀ i : Fin 3, codeTest (69+i.val) := joinChunks (P := codeTest) (start := 69) (a := 1) (b := 2) codeTest_69_70 codeTest_70_72

private theorem codeTest_67_72 : ∀ i : Fin 5, codeTest (67+i.val) := joinChunks (P := codeTest) (start := 67) (a := 2) (b := 3) codeTest_67_69 codeTest_69_72

private theorem codeTest_62_72 : ∀ i : Fin 10, codeTest (62+i.val) := joinChunks (P := codeTest) (start := 62) (a := 5) (b := 5) codeTest_62_67 codeTest_67_72

private theorem codeTest_72_73 : ∀ i : Fin 1, codeTest (72+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_73_74 : ∀ i : Fin 1, codeTest (73+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_72_74 : ∀ i : Fin 2, codeTest (72+i.val) := joinChunks (P := codeTest) (start := 72) (a := 1) (b := 1) codeTest_72_73 codeTest_73_74

private theorem codeTest_74_75 : ∀ i : Fin 1, codeTest (74+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_75_76 : ∀ i : Fin 1, codeTest (75+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_76_77 : ∀ i : Fin 1, codeTest (76+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_75_77 : ∀ i : Fin 2, codeTest (75+i.val) := joinChunks (P := codeTest) (start := 75) (a := 1) (b := 1) codeTest_75_76 codeTest_76_77

private theorem codeTest_74_77 : ∀ i : Fin 3, codeTest (74+i.val) := joinChunks (P := codeTest) (start := 74) (a := 1) (b := 2) codeTest_74_75 codeTest_75_77

private theorem codeTest_72_77 : ∀ i : Fin 5, codeTest (72+i.val) := joinChunks (P := codeTest) (start := 72) (a := 2) (b := 3) codeTest_72_74 codeTest_74_77

private theorem codeTest_77_78 : ∀ i : Fin 1, codeTest (77+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_78_79 : ∀ i : Fin 1, codeTest (78+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_79_80 : ∀ i : Fin 1, codeTest (79+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_78_80 : ∀ i : Fin 2, codeTest (78+i.val) := joinChunks (P := codeTest) (start := 78) (a := 1) (b := 1) codeTest_78_79 codeTest_79_80

private theorem codeTest_77_80 : ∀ i : Fin 3, codeTest (77+i.val) := joinChunks (P := codeTest) (start := 77) (a := 1) (b := 2) codeTest_77_78 codeTest_78_80

private theorem codeTest_80_81 : ∀ i : Fin 1, codeTest (80+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_81_82 : ∀ i : Fin 1, codeTest (81+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_82_83 : ∀ i : Fin 1, codeTest (82+i.val) := by unfold codeTest; decide +kernel

private theorem codeTest_81_83 : ∀ i : Fin 2, codeTest (81+i.val) := joinChunks (P := codeTest) (start := 81) (a := 1) (b := 1) codeTest_81_82 codeTest_82_83

private theorem codeTest_80_83 : ∀ i : Fin 3, codeTest (80+i.val) := joinChunks (P := codeTest) (start := 80) (a := 1) (b := 2) codeTest_80_81 codeTest_81_83

private theorem codeTest_77_83 : ∀ i : Fin 6, codeTest (77+i.val) := joinChunks (P := codeTest) (start := 77) (a := 3) (b := 3) codeTest_77_80 codeTest_80_83

private theorem codeTest_72_83 : ∀ i : Fin 11, codeTest (72+i.val) := joinChunks (P := codeTest) (start := 72) (a := 5) (b := 6) codeTest_72_77 codeTest_77_83

private theorem codeTest_62_83 : ∀ i : Fin 21, codeTest (62+i.val) := joinChunks (P := codeTest) (start := 62) (a := 10) (b := 11) codeTest_62_72 codeTest_72_83

private theorem codeTest_41_83 : ∀ i : Fin 42, codeTest (41+i.val) := joinChunks (P := codeTest) (start := 41) (a := 21) (b := 21) codeTest_41_62 codeTest_62_83

private theorem codeTest_0_83 : ∀ i : Fin 83, codeTest (0+i.val) := joinChunks (P := codeTest) (start := 0) (a := 41) (b := 42) codeTest_0_41 codeTest_41_83

theorem code_order (i j : Label) (h : code i ⊆ code j) : row i &&& row j = row i := by
  have t := codeTest_0_83 i
  simpa [Fin.ofNat,Nat.mod_eq_of_lt i.isLt] using t j (by simpa [Fin.ofNat,Nat.mod_eq_of_lt i.isLt] using h)


end PEqualNP.Research.ColourProfiles18173

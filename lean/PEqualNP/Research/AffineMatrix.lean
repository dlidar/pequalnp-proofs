import Mathlib

namespace PEqualNP.Research.AffineRectangleCover
open Finset
abbrev P := Fin 25
abbrev L := Fin 30
abbrev Box := Finset P × Finset L
def rows : List Nat := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def zero (p : P) (l : L) : Bool := !(rows.getD p.val 0).testBit l.val
end PEqualNP.Research.AffineRectangleCover

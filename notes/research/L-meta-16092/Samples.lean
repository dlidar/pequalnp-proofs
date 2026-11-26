import Signed16092
namespace PEqualNP.Research.Signed16092
def rows : List W := [0x87d0666876da1db6d5f1fff87ffe1fff, 0x592c888f05b7c16dffee888f87ffe1ff, 0xef1b0f0ee8e3ba382a1f0f0ff8e3fe38, 0x31e7f00ddf0377c02a1ff00fff03ffc0, 0xfaafddd00000eedb873ffff00003ffff, 0x7c7fbbb3bb6c000078cffffffffc0000]
theorem samples : ∀ k : Fin 128, F5 (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel
end PEqualNP.Research.Signed16092

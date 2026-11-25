import PEqualNP.Research.L_meta_2341_data

namespace PEqualNP.Research.PuncturedFlags
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
theorem positive_rows : ∀ p l : Fin 13, (∃ i, pos i=edge p l) ↔ inc p l ∧ (p ≠ 0 ∨ l ≠ 0) := by decide +kernel
theorem positive_shape : ∀ i, ∃ (p l : Fin 13), pos i=edge p l := by decide +kernel
theorem negative_rows : ∀ j : Fin 234, quad (points (neg j)) ∧
    ∀ l : Fin 13, (neg j).testBit (13+l.val) = decide (∀ p ∈ points (neg j), ¬ inc p l) := by decide +kernel
theorem row_sizes : ∀ j : Fin 234, neg j < 2^26 := by decide +kernel

def index (q : ℕ) : ℕ := (if q < 2130 then (if q < 774 then (if q < 308 then (if q < 154 then (if q < 85 then (if q < 71 then (if q < 39 then 18 else (if q < 58 then 0 else 86)) else (if q < 78 then (if q < 77 then 1 else 19) else (if q < 83 then 72 else 4))) else (if q < 116 then (if q < 101 then 22 else (if q < 105 then 25 else 35)) else (if q < 141 then (if q < 135 then 136 else 2) else (if q < 142 then 20 else 73)))) else (if q < 210 then (if q < 170 then (if q < 156 then 87 else (if q < 166 then 126 else 76)) else (if q < 201 then (if q < 195 then 90 else 11) else (if q < 202 then 39 else 93))) else (if q < 281 then (if q < 270 then (if q < 232 then 103 else 173) else (if q < 275 then 74 else 5)) else (if q < 284 then (if q < 282 then 32 else 88) else (if q < 297 then 127 else 36))))) else (if q < 540 then (if q < 390 then (if q < 332 then (if q < 312 then 137 else (if q < 329 then 166 else 40)) else (if q < 340 then (if q < 337 then 129 else 46) else (if q < 387 then 140 else 13))) else (if q < 420 then (if q < 402 then 81 else (if q < 404 then 106 else 142)) else (if q < 464 then (if q < 449 then 149 else 60) else (if q < 533 then 199 else 23)))) else (if q < 594 then (if q < 562 then (if q < 549 then 128 else (if q < 550 then 26 else 77)) else (if q < 568 then (if q < 564 then 100 else 138) else (if q < 593 then 167 else 47))) else (if q < 658 then (if q < 616 then (if q < 609 then 104 else 53) else (if q < 624 then 174 else 192)) else (if q < 674 then (if q < 664 then 107 else 169) else (if q < 680 then 110 else 176)))))) else (if q < 1283 then (if q < 1065 then (if q < 897 then (if q < 804 then (if q < 780 then 82 else (if q < 801 then 132 else 55)) else (if q < 833 then (if q < 808 then 152 else 178) else (if q < 840 then 62 else 181))) else (if q < 1037 then (if q < 898 then 64 else (if q < 928 then 119 else 216)) else (if q < 1059 then (if q < 1049 then 21 else 33) else (if q < 1061 then 8 else 27)))) else (if q < 1136 then (if q < 1098 then (if q < 1066 then 37 else (if q < 1080 then 91 else 168)) else (if q < 1124 then (if q < 1100 then 94 else 130) else (if q < 1128 then 147 else 175))) else (if q < 1188 then (if q < 1157 then (if q < 1155 then 193 else 14) else (if q < 1186 then 28 else 111)) else (if q < 1232 then (if q < 1218 then 150 else 114) else (if q < 1248 then 200 else 211))))) else (if q < 1666 then (if q < 1541 then (if q < 1316 then (if q < 1297 then 15 else (if q < 1313 then 48 else 56)) else (if q < 1348 then (if q < 1328 then 153 else 195) else (if q < 1360 then 154 else 202))) else (if q < 1602 then (if q < 1553 then (if q < 1548 then 30 else 133) else (if q < 1560 then 49 else 171)) else (if q < 1616 then (if q < 1608 then 115 else 183) else (if q < 1665 then 203 else 66)))) else (if q < 2067 then (if q < 1794 then (if q < 1680 then 120 else (if q < 1793 then 205 else 70)) else (if q < 1856 then (if q < 1796 then 121 else 161) else (if q < 2055 then 226 else 3))) else (if q < 2083 then (if q < 2073 then (if q < 2069 then 6 else 24) else (if q < 2074 then 34 else 89)) else (if q < 2118 then (if q < 2098 then 9 else 101) else (if q < 2122 then 79 else 95))))))) else (if q < 4236 then (if q < 2696 then (if q < 2337 then (if q < 2248 then (if q < 2181 then (if q < 2132 then 105 else (if q < 2160 then 141 else 194)) else (if q < 2196 then (if q < 2185 then 29 else 41) else (if q < 2200 then 143 else 170))) else (if q < 2307 then (if q < 2256 then 180 else (if q < 2272 then 201 else 212)) else (if q < 2313 then (if q < 2310 then 16 else 83) else (if q < 2314 then 43 else 96)))) else (if q < 2565 then (if q < 2433 then (if q < 2372 then 57 else (if q < 2376 then 155 else 182)) else (if q < 2464 then (if q < 2436 then 65 else 158) else (if q < 2496 then 217 else 223))) else (if q < 2626 then (if q < 2593 then (if q < 2566 then 31 else 84) else (if q < 2594 then 58 else 112)) else (if q < 2656 then (if q < 2632 then 116 else 184) else (if q < 2689 then 214 else 67))))) else (if q < 3592 then (if q < 3216 then (if q < 3096 then (if q < 2720 then 185 else (if q < 3082 then 219 else 98)) else (if q < 3120 then (if q < 3106 then 172 else 113) else (if q < 3204 then 197 else 159))) else (if q < 3332 then (if q < 3232 then 207 else (if q < 3330 then 220 else 123)) else (if q < 3586 then (if q < 3360 then 162 else 221) else (if q < 3588 then 125 else 163)))) else (if q < 4138 then (if q < 4115 then (if q < 3712 then 189 else (if q < 4110 then 232 else 75)) else (if q < 4134 then (if q < 4131 then 7 else 10) else (if q < 4137 then 78 else 38))) else (if q < 4166 then (if q < 4148 then (if q < 4146 then 92 else 102) else (if q < 4163 then 139 else 12)) else (if q < 4196 then (if q < 4193 then 80 else 54) else (if q < 4233 then 148 else 42)))))) else (if q < 5130 then (if q < 4620 then (if q < 4370 then (if q < 4264 then (if q < 4244 then 131 else (if q < 4260 then 144 else 151)) else (if q < 4320 then (if q < 4289 then 177 else 61) else (if q < 4362 then 213 else 97))) else (if q < 4496 then (if q < 4392 then 108 else (if q < 4400 then 179 else 196)) else (if q < 4544 then (if q < 4512 then 204 else 218) else (if q < 4614 then 224 else 85)))) else (if q < 4744 then (if q < 4628 then (if q < 4625 then 134 else (if q < 4626 then 50 else 109)) else (if q < 4674 then (if q < 4673 then 145 else 63) else (if q < 4737 then 117 else 68))) else (if q < 4928 then (if q < 4866 then (if q < 4752 then 186 else 206) else (if q < 4872 then 122 else 187)) else (if q < 5123 then (if q < 4992 then 227 else 231) else (if q < 5129 then 17 else 44))))) else (if q < 6177 then (if q < 5264 then (if q < 5186 then (if q < 5132 then 99 else (if q < 5137 then 135 else 51)) else (if q < 5249 then (if q < 5188 then 118 else 156) else (if q < 5252 then 69 else 160))) else (if q < 5440 then (if q < 5378 then (if q < 5312 then 208 else 225) else (if q < 5392 then 124 else 209)) else (if q < 6161 then (if q < 6153 then 228 else 45) else (if q < 6164 then 52 else 146)))) else (if q < 6657 then (if q < 6240 then (if q < 6192 then 59 else (if q < 6212 then 198 else 157)) else (if q < 6432 then (if q < 6408 then 215 else 188) else (if q < 6464 then 222 else 229))) else (if q < 7172 then (if q < 6664 then (if q < 6660 then 71 else 164) else (if q < 6720 then 190 else 230)) else (if q < 7184 then (if q < 7176 then 165 else 191) else (if q < 7424 then 210 else 233))))))))
def rowOf (q : ℕ) : Fin 234 := Fin.ofNat 234 (index q)

def mask (S : Finset (Fin 13)) : Fin 8192 :=
  ⟨Nat.ofBits (fun p : Fin 13 => decide (p ∈ S)),Nat.ofBits_lt_two_pow _⟩
theorem recover (S : Finset (Fin 13)) : points (mask S).val = S := by
  ext p
  simp [points,mask,Nat.testBit_ofBits_lt _ _ p.isLt]

private theorem block0 : ∀ low : Fin 128, let q := 128*0+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block1 : ∀ low : Fin 128, let q := 128*1+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block2 : ∀ low : Fin 128, let q := 128*2+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block3 : ∀ low : Fin 128, let q := 128*3+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block4 : ∀ low : Fin 128, let q := 128*4+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block5 : ∀ low : Fin 128, let q := 128*5+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block6 : ∀ low : Fin 128, let q := 128*6+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block7 : ∀ low : Fin 128, let q := 128*7+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block8 : ∀ low : Fin 128, let q := 128*8+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block9 : ∀ low : Fin 128, let q := 128*9+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block10 : ∀ low : Fin 128, let q := 128*10+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block11 : ∀ low : Fin 128, let q := 128*11+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block12 : ∀ low : Fin 128, let q := 128*12+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block13 : ∀ low : Fin 128, let q := 128*13+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block14 : ∀ low : Fin 128, let q := 128*14+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block15 : ∀ low : Fin 128, let q := 128*15+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block16 : ∀ low : Fin 128, let q := 128*16+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block17 : ∀ low : Fin 128, let q := 128*17+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block18 : ∀ low : Fin 128, let q := 128*18+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block19 : ∀ low : Fin 128, let q := 128*19+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block20 : ∀ low : Fin 128, let q := 128*20+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block21 : ∀ low : Fin 128, let q := 128*21+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block22 : ∀ low : Fin 128, let q := 128*22+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block23 : ∀ low : Fin 128, let q := 128*23+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block24 : ∀ low : Fin 128, let q := 128*24+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block25 : ∀ low : Fin 128, let q := 128*25+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block26 : ∀ low : Fin 128, let q := 128*26+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block27 : ∀ low : Fin 128, let q := 128*27+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block28 : ∀ low : Fin 128, let q := 128*28+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block29 : ∀ low : Fin 128, let q := 128*29+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block30 : ∀ low : Fin 128, let q := 128*30+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block31 : ∀ low : Fin 128, let q := 128*31+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block32 : ∀ low : Fin 128, let q := 128*32+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block33 : ∀ low : Fin 128, let q := 128*33+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block34 : ∀ low : Fin 128, let q := 128*34+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block35 : ∀ low : Fin 128, let q := 128*35+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block36 : ∀ low : Fin 128, let q := 128*36+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block37 : ∀ low : Fin 128, let q := 128*37+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block38 : ∀ low : Fin 128, let q := 128*38+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block39 : ∀ low : Fin 128, let q := 128*39+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block40 : ∀ low : Fin 128, let q := 128*40+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block41 : ∀ low : Fin 128, let q := 128*41+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block42 : ∀ low : Fin 128, let q := 128*42+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block43 : ∀ low : Fin 128, let q := 128*43+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block44 : ∀ low : Fin 128, let q := 128*44+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block45 : ∀ low : Fin 128, let q := 128*45+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block46 : ∀ low : Fin 128, let q := 128*46+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block47 : ∀ low : Fin 128, let q := 128*47+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block48 : ∀ low : Fin 128, let q := 128*48+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block49 : ∀ low : Fin 128, let q := 128*49+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block50 : ∀ low : Fin 128, let q := 128*50+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block51 : ∀ low : Fin 128, let q := 128*51+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block52 : ∀ low : Fin 128, let q := 128*52+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block53 : ∀ low : Fin 128, let q := 128*53+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block54 : ∀ low : Fin 128, let q := 128*54+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block55 : ∀ low : Fin 128, let q := 128*55+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block56 : ∀ low : Fin 128, let q := 128*56+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block57 : ∀ low : Fin 128, let q := 128*57+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block58 : ∀ low : Fin 128, let q := 128*58+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block59 : ∀ low : Fin 128, let q := 128*59+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block60 : ∀ low : Fin 128, let q := 128*60+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block61 : ∀ low : Fin 128, let q := 128*61+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block62 : ∀ low : Fin 128, let q := 128*62+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
private theorem block63 : ∀ low : Fin 128, let q := 128*63+low.val; quad (points q) → points (neg (rowOf q)) = points q := by decide +kernel
theorem table_complete (Q : Finset (Fin 13)) (hq : quad Q) : ∃ j, points (neg j) = Q := by
  let q := (mask Q).val
  have small : q < 8192 := (mask Q).isLt
  let lo : Fin 128 := ⟨q%128, Nat.mod_lt _ (by decide)⟩
  let hi : Fin 64 := ⟨q/128, by omega⟩
  have split : q = 128*hi.val+lo.val := by dsimp [hi,lo]; omega
  have H : ∀ b : Fin 64, let x := 128*b.val+lo.val; quad (points x) → points (neg (rowOf x)) = points x := by
    intro b; fin_cases b
    · exact block0 lo
    · exact block1 lo
    · exact block2 lo
    · exact block3 lo
    · exact block4 lo
    · exact block5 lo
    · exact block6 lo
    · exact block7 lo
    · exact block8 lo
    · exact block9 lo
    · exact block10 lo
    · exact block11 lo
    · exact block12 lo
    · exact block13 lo
    · exact block14 lo
    · exact block15 lo
    · exact block16 lo
    · exact block17 lo
    · exact block18 lo
    · exact block19 lo
    · exact block20 lo
    · exact block21 lo
    · exact block22 lo
    · exact block23 lo
    · exact block24 lo
    · exact block25 lo
    · exact block26 lo
    · exact block27 lo
    · exact block28 lo
    · exact block29 lo
    · exact block30 lo
    · exact block31 lo
    · exact block32 lo
    · exact block33 lo
    · exact block34 lo
    · exact block35 lo
    · exact block36 lo
    · exact block37 lo
    · exact block38 lo
    · exact block39 lo
    · exact block40 lo
    · exact block41 lo
    · exact block42 lo
    · exact block43 lo
    · exact block44 lo
    · exact block45 lo
    · exact block46 lo
    · exact block47 lo
    · exact block48 lo
    · exact block49 lo
    · exact block50 lo
    · exact block51 lo
    · exact block52 lo
    · exact block53 lo
    · exact block54 lo
    · exact block55 lo
    · exact block56 lo
    · exact block57 lo
    · exact block58 lo
    · exact block59 lo
    · exact block60 lo
    · exact block61 lo
    · exact block62 lo
    · exact block63 lo
  have eq : points q = Q := recover Q
  have h := H hi
  dsimp only at h
  rw [←split] at h
  exact ⟨rowOf q,(h (eq.symm ▸ hq)).trans eq⟩

end PEqualNP.Research.PuncturedFlags

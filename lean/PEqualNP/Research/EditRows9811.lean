import Mathlib
namespace PEqualNP.Research.EditRows9811
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
abbrev Input := BitVec 14
abbrev Edge := Fin 14 × Fin 14
def hit (e : Edge) (x : Input) := x.getLsbD e.1.val && x.getLsbD e.2.val
def graph (es : List Edge) (x : Input) := es.any fun e => hit e x
def target : List Edge := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def allEdges : List Edge := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 10), (9, 11), (9, 12), (9, 13), (10, 11), (10, 12), (10, 13), (11, 12), (11, 13), (12, 13)]
/-- There are k distinct 14-bit inputs on which the predicates disagree. -/
def separated (k : Nat) (fs : List Edge) := ∃ xs : List Input, xs.length = k ∧
  xs.Nodup ∧ ∀ x ∈ xs, graph target x ≠ graph fs x
def addOK (p : Edge) (xs : List Input) := xs.all (fun x => hit p x && !graph target x)
def delOK (p : Edge) (xs : List Input) := xs.all (fun x => hit p x &&
  !(target.any (fun e => decide (e ≠ p) && hit e x)))
private theorem row0 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 1) xs = true :=
  ⟨([3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63, 67, 71] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row1 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 2) xs = true :=
  ⟨([5, 7, 13, 15, 21, 23, 29, 31, 37, 39, 45, 47, 53, 55, 61, 63, 69, 71] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row2 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 3) xs = true :=
  ⟨([9, 11, 13, 15, 25, 27, 29, 31, 41, 43, 45, 47, 57, 59, 61, 63, 73, 75] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row3 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 4) xs = true :=
  ⟨([17, 19, 21, 23, 25, 27, 29, 31, 49, 51, 53, 55, 57, 59, 61, 63, 81, 83] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row4 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 5) xs = true :=
  ⟨([33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 97, 99] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row5 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 6) xs = true :=
  ⟨([65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row6 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 7) xs = true :=
  ⟨([129, 133, 145, 149, 161, 165, 177, 181, 193, 197, 209, 213, 225, 229, 241, 245, 641, 645] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row7 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (0, 8) xs = true :=
  ⟨([257, 259, 265, 267, 273, 275, 281, 283, 289, 291, 297, 299, 305, 307, 313, 315, 385, 401, 417, 433, 769, 771, 777, 779, 785, 787, 793, 795, 897, 913, 2305, 2307, 2337, 2339, 2433, 2465, 2817, 2819, 2945, 4353, 4355, 4369, 4371, 4481, 4497, 4865, 4867] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row8 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 9) xs = true :=
  ⟨([513, 515, 517, 519, 521, 523, 525, 527, 529, 531, 533, 535, 537, 539, 541, 543, 641, 645] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row9 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (0, 10) xs = true :=
  ⟨([1025, 1027, 1029, 1031, 1033, 1035, 1037, 1039, 1089, 1091, 1093, 1095, 1097, 1099, 1101, 1103, 1153, 1157, 1217, 1221, 1537, 1539, 1541, 1543, 1545, 1547, 1549, 1551, 1665, 1669, 3073, 3075, 3077, 3079, 3201, 3205, 3585, 3587, 3589, 3591, 3713, 3717, 5121, 5123, 5185, 5187, 5249] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row10 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 11) xs = true :=
  ⟨([2049, 2051, 2053, 2055, 2081, 2083, 2085, 2087, 2177, 2181, 2209, 2213, 2561, 2563, 2565, 2567, 2689, 2693] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row11 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 12) xs = true :=
  ⟨([4097, 4099, 4113, 4115, 4161, 4163, 4177, 4179, 4225, 4241, 4289, 4305, 4609, 4611, 4625, 4627, 4737, 4753] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row12 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (0, 13) xs = true :=
  ⟨([8193, 8201, 8225, 8233, 8257, 8265, 8289, 8297, 8321, 8353, 8385, 8417, 8705, 8713, 8833, 10241, 10273, 10369] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row13 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 2) xs = true :=
  ⟨([6, 7, 14, 15, 22, 23, 30, 31, 38, 39, 46, 47, 54, 55, 62, 63, 70, 71] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row14 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 3) xs = true :=
  ⟨([10, 11, 14, 15, 26, 27, 30, 31, 42, 43, 46, 47, 58, 59, 62, 63, 74, 75] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row15 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 4) xs = true :=
  ⟨([18, 19, 22, 23, 26, 27, 30, 31, 50, 51, 54, 55, 58, 59, 62, 63, 82, 83] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row16 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 5) xs = true :=
  ⟨([34, 35, 38, 39, 42, 43, 46, 47, 50, 51, 54, 55, 58, 59, 62, 63, 98, 99] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row17 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 6) xs = true :=
  ⟨([66, 67, 70, 71, 74, 75, 78, 79, 82, 83, 86, 87, 90, 91, 94, 95, 98, 99] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row18 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (1, 7) xs = true :=
  ⟨([130, 131, 134, 135, 146, 147, 150, 151, 162, 163, 166, 167, 178, 179, 182, 183, 194, 195, 198, 199, 210, 211, 214, 215, 226, 227, 230, 231, 242, 243, 246, 247, 386, 402, 418, 434, 642, 643, 646, 647, 658, 659, 662, 663, 898, 914, 1154] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row19 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 8) xs = true :=
  ⟨([258, 266, 274, 282, 290, 298, 306, 314, 770, 778, 786, 794, 1282, 1290, 1794, 1802, 2306, 2338] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row20 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 9) xs = true :=
  ⟨([514, 515, 518, 519, 522, 523, 526, 527, 530, 531, 534, 535, 538, 539, 542, 543, 770, 778] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row21 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 10) xs = true :=
  ⟨([1026, 1030, 1034, 1038, 1090, 1094, 1098, 1102, 1282, 1290, 1538, 1542, 1546, 1550, 1794, 1802, 3074, 3078] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row22 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 11) xs = true :=
  ⟨([2050, 2051, 2054, 2055, 2082, 2083, 2086, 2087, 2306, 2338, 2562, 2563, 2566, 2567, 2818, 3074, 3078, 3330] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row23 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (1, 12) xs = true :=
  ⟨([4098, 4099, 4114, 4115, 4162, 4163, 4178, 4179, 4354, 4370, 4610, 4611, 4626, 4627, 4866, 4882, 5122, 5186] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row24 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (1, 13) xs = true :=
  ⟨([8194, 8195, 8202, 8203, 8226, 8227, 8234, 8235, 8258, 8259, 8266, 8267, 8290, 8291, 8298, 8299, 8450, 8458, 8482, 8490, 8706, 8707, 8714, 8715, 8962, 8970, 9218, 9226, 9282, 9290, 9474, 9482, 9730, 9738, 9986, 9994, 10242, 10243, 10274, 10275, 10498, 10530, 10754, 10755, 11010, 11266, 11522] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row25 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 3) xs = true :=
  ⟨([12, 13, 14, 15, 28, 29, 30, 31, 44, 45, 46, 47, 60, 61, 62, 63, 76, 77] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row26 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 4) xs = true :=
  ⟨([20, 21, 22, 23, 28, 29, 30, 31, 52, 53, 54, 55, 60, 61, 62, 63, 84, 85] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row27 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 5) xs = true :=
  ⟨([36, 37, 38, 39, 44, 45, 46, 47, 52, 53, 54, 55, 60, 61, 62, 63, 100, 101] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row28 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 6) xs = true :=
  ⟨([68, 69, 70, 71, 76, 77, 78, 79, 84, 85, 86, 87, 92, 93, 94, 95, 100, 101] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row29 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 7) xs = true :=
  ⟨([132, 133, 148, 149, 164, 165, 180, 181, 196, 197, 212, 213, 228, 229, 244, 245, 644, 645] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row30 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (2, 8) xs = true :=
  ⟨([260, 262, 268, 270, 276, 278, 284, 286, 292, 294, 300, 302, 308, 310, 316, 318, 388, 404, 420, 436, 772, 774, 780, 782, 788, 790, 796, 798, 900, 916, 1284, 1286, 1292, 1294, 1412, 1796, 1798, 1804, 1806, 1924, 2308, 2310, 2340, 2342, 2436, 2468, 2820] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row31 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 9) xs = true :=
  ⟨([516, 517, 518, 519, 524, 525, 526, 527, 532, 533, 534, 535, 540, 541, 542, 543, 644, 645] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row32 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 10) xs = true :=
  ⟨([1028, 1030, 1036, 1038, 1092, 1094, 1100, 1102, 1156, 1220, 1540, 1542, 1548, 1550, 1668, 3076, 3078, 3204] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row33 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (2, 11) xs = true :=
  ⟨([2052, 2053, 2054, 2055, 2084, 2085, 2086, 2087, 2180, 2181, 2212, 2213, 2564, 2565, 2566, 2567, 2692, 2693] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row34 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (2, 12) xs = true :=
  ⟨([4100, 4101, 4102, 4103, 4116, 4117, 4118, 4119, 4164, 4165, 4166, 4167, 4180, 4181, 4182, 4183, 4228, 4229, 4244, 4245, 4292, 4293, 4308, 4309, 4612, 4613, 4614, 4615, 4628, 4629, 4630, 4631, 4740, 4741, 4756, 4757, 5124, 5126, 5188, 5190, 5252, 5316, 5636, 5638, 5764, 6148, 6149] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row35 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (2, 13) xs = true :=
  ⟨([8196, 8197, 8204, 8205, 8228, 8229, 8236, 8237, 8260, 8261, 8268, 8269, 8292, 8293, 8300, 8301, 8324, 8325, 8356, 8357, 8388, 8389, 8420, 8421, 8708, 8709, 8716, 8717, 8836, 8837, 9220, 9228, 9284, 9292, 9348, 9412, 9732, 9740, 9860, 10244, 10245, 10276, 10277, 10372, 10373, 10404, 10405] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row36 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 4) xs = true :=
  ⟨([24, 25, 26, 27, 28, 29, 30, 31, 56, 57, 58, 59, 60, 61, 62, 63, 88, 89] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row37 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 5) xs = true :=
  ⟨([40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63, 104, 105] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row38 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 6) xs = true :=
  ⟨([72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95, 104, 105] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row39 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (3, 7) xs = true :=
  ⟨([136, 137, 140, 141, 152, 153, 156, 157, 168, 169, 172, 173, 184, 185, 188, 189, 200, 201, 204, 205, 216, 217, 220, 221, 232, 233, 236, 237, 248, 249, 252, 253, 392, 408, 424, 440, 648, 649, 652, 653, 664, 665, 668, 669, 904, 920, 1160] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row40 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 8) xs = true :=
  ⟨([264, 266, 280, 282, 296, 298, 312, 314, 776, 778, 792, 794, 1288, 1290, 1800, 1802, 8456, 8488] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row41 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 9) xs = true :=
  ⟨([520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 776, 778] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row42 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 10) xs = true :=
  ⟨([1032, 1034, 1036, 1038, 1096, 1098, 1100, 1102, 1288, 1290, 1544, 1546, 1548, 1550, 1800, 1802, 9224, 9288] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row43 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (3, 11) xs = true :=
  ⟨([2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095, 2312, 2314, 2344, 2346, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575, 2824, 2826, 3080, 3082, 3084, 3086, 3336, 3338, 3592, 3594, 3596, 3598, 3848, 3850, 10248, 10249, 10280, 10281, 10504] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row44 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (3, 12) xs = true :=
  ⟨([4104, 4105, 4106, 4107, 4120, 4121, 4122, 4123, 4168, 4169, 4170, 4171, 4184, 4185, 4186, 4187, 4360, 4362, 4376, 4378, 4616, 4617, 4618, 4619, 4632, 4633, 4634, 4635, 4872, 4874, 4888, 4890, 5128, 5130, 5192, 5194, 5384, 5386, 5640, 5642, 5896, 5898, 12296, 12297, 12360, 12361, 12552] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row45 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (3, 13) xs = true :=
  ⟨([8200, 8201, 8232, 8233, 8264, 8265, 8296, 8297, 8456, 8488, 8712, 8713, 8968, 9224, 9288, 9480, 9736, 9992] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row46 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 5) xs = true :=
  ⟨([48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 112, 113] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row47 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 6) xs = true :=
  ⟨([80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 112, 113] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row48 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 7) xs = true :=
  ⟨([144, 145, 148, 149, 176, 177, 180, 181, 208, 209, 212, 213, 240, 241, 244, 245, 400, 432] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row49 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 8) xs = true :=
  ⟨([272, 274, 280, 282, 304, 306, 312, 314, 400, 432, 784, 786, 792, 794, 912, 4368, 4370, 4496] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row50 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 9) xs = true :=
  ⟨([528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 656, 657] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row51 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (4, 10) xs = true :=
  ⟨([1040, 1042, 1044, 1046, 1048, 1050, 1052, 1054, 1104, 1106, 1108, 1110, 1112, 1114, 1116, 1118, 1168, 1172, 1232, 1236, 1296, 1298, 1304, 1306, 1424, 1552, 1554, 1556, 1558, 1560, 1562, 1564, 1566, 1680, 1684, 1808, 1810, 1816, 1818, 1936, 5136, 5138, 5200, 5202, 5264, 5328, 5392] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row52 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (4, 11) xs = true :=
  ⟨([2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2192, 2193, 2196, 2197, 2224, 2225, 2228, 2229, 2320, 2322, 2352, 2354, 2448, 2480, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2704, 2705, 2708, 2709, 2832, 2834, 2960, 6160, 6161] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row53 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (4, 12) xs = true :=
  ⟨([4112, 4113, 4114, 4115, 4176, 4177, 4178, 4179, 4240, 4241, 4304, 4305, 4368, 4370, 4496, 4624, 4625, 4626] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row54 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (4, 13) xs = true :=
  ⟨([8208, 8209, 8216, 8217, 8240, 8241, 8248, 8249, 8272, 8273, 8280, 8281, 8304, 8305, 8312, 8313, 8336, 8337, 8368, 8369, 8400, 8401, 8432, 8433, 8464, 8472, 8496, 8504, 8592, 8624, 8720, 8721, 8728, 8729, 8848, 8849, 8976, 8984, 9104, 12304, 12305, 12368, 12369, 12432, 12433, 12496, 12497] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row55 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (5, 6) xs = true :=
  ⟨([96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row56 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (5, 7) xs = true :=
  ⟨([160, 161, 164, 165, 176, 177, 180, 181, 224, 225, 228, 229, 240, 241, 244, 245, 416, 432] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row57 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (5, 8) xs = true :=
  ⟨([288, 290, 296, 298, 304, 306, 312, 314, 416, 432, 2336, 2338, 2464, 8480, 8488, 8608, 10528, 10656] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row58 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (5, 9) xs = true :=
  ⟨([544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 672, 673, 676, 677, 688, 689, 692, 693, 800, 802, 808, 810, 816, 818, 824] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row59 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (5, 10) xs = true :=
  ⟨([1056, 1058, 1060, 1062, 1064, 1066, 1068, 1070, 1120, 1122, 1124, 1126, 1128, 1130, 1132, 1134, 1184, 1188, 1248, 1252, 1312, 1314, 1320, 1322, 1440, 3104, 3106, 3108, 3110, 3232, 3236, 3360, 3362, 3488, 9248, 9256, 9312, 9320, 9376, 9440, 9504, 9512, 9632, 11296, 11424, 11552, 11680] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row60 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (5, 11) xs = true :=
  ⟨([2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2208, 2209, 2212, 2213, 2336, 2338, 2464, 10272, 10273, 10400] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row61 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (5, 12) xs = true :=
  ⟨([4128, 4129, 4130, 4131, 4144, 4145, 4146, 4147, 4192, 4193, 4194, 4195, 4208, 4209, 4210, 4211, 4256, 4257, 4272, 4273, 4320, 4321, 4336, 4337, 4384, 4386, 4400, 4402, 4512, 4528, 6176, 6177, 6178, 6179, 6304, 6305, 6432, 6434, 6560, 12320, 12321, 12384, 12385, 12448, 12449, 12512, 12513] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row62 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (5, 13) xs = true :=
  ⟨([8224, 8225, 8232, 8233, 8288, 8289, 8296, 8297, 8352, 8353, 8416, 8417, 8480, 8488, 8608, 10272, 10273, 10400] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row63 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (6, 7) xs = true :=
  ⟨([192, 193, 196, 197, 208, 209, 212, 213, 224, 225, 228, 229, 240, 241, 244, 245, 1216, 1220] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row64 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (6, 8) xs = true :=
  ⟨([320, 322, 328, 330, 336, 338, 344, 346, 352, 354, 360, 362, 368, 370, 376, 378, 448, 464, 480, 496, 1344, 1346, 1352, 1354, 1472, 4416, 4418, 4432, 4434, 4544, 4560, 5440, 5442, 5568, 8512, 8520, 8544, 8552, 8640, 8672, 9536, 9544, 9664, 12608, 12736, 13632, 13760] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row65 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (6, 9) xs = true :=
  ⟨([576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 704, 705, 708, 709, 720, 721, 724, 725, 1600, 1602, 1604, 1606, 1608, 1610, 1612] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row66 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (6, 10) xs = true :=
  ⟨([1088, 1090, 1092, 1094, 1096, 1098, 1100, 1102, 1216, 1220, 5184, 5186, 5312, 9280, 9288, 9408, 13376, 13504] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row67 : ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK (6, 11) xs = true :=
  ⟨([2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2240, 2241, 2244, 2245, 2272, 2273, 2276, 2277, 3136, 3138, 3140, 3142, 3264, 3268, 6208, 6209, 6210, 6211, 6336, 6337, 7232, 7234, 7360, 10304, 10305, 10336, 10337, 10432, 10433, 10464, 10465] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row68 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (6, 12) xs = true :=
  ⟨([4160, 4161, 4162, 4163, 4176, 4177, 4178, 4179, 4288, 4289, 4304, 4305, 5184, 5186, 5312, 12352, 12353, 12480] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row69 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (6, 13) xs = true :=
  ⟨([8256, 8257, 8264, 8265, 8288, 8289, 8296, 8297, 8384, 8385, 8416, 8417, 9280, 9288, 9408, 12352, 12353, 12480] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row70 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 8) xs = true :=
  ⟨([384, 400, 416, 432, 896, 912, 1408, 1920, 2432, 2464, 2944, 3456, 3968, 4480, 4496, 4992, 5008, 5504] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row71 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 9) xs = true :=
  ⟨([640, 641, 644, 645, 656, 657, 660, 661, 896, 912, 1664, 1668, 1920, 2688, 2689, 2692, 2693, 2944] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row72 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 10) xs = true :=
  ⟨([1152, 1156, 1216, 1220, 1408, 1664, 1668, 1920, 3200, 3204, 3456, 3712, 3716, 3968, 5248, 5312, 5504, 5760] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row73 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 11) xs = true :=
  ⟨([2176, 2177, 2180, 2181, 2208, 2209, 2212, 2213, 2432, 2464, 2688, 2689, 2692, 2693, 2944, 3200, 3204, 3456] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row74 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 12) xs = true :=
  ⟨([4224, 4225, 4240, 4241, 4288, 4289, 4304, 4305, 4480, 4496, 4736, 4737, 4752, 4753, 4992, 5008, 5248, 5312] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row75 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (7, 13) xs = true :=
  ⟨([8320, 8321, 8352, 8353, 8384, 8385, 8416, 8417, 8576, 8608, 8832, 8833, 9088, 9344, 9408, 9600, 9856, 10112] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row76 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (8, 9) xs = true :=
  ⟨([768, 770, 776, 778, 784, 786, 792, 794, 896, 912, 1792, 1794, 1800, 1802, 1920, 2816, 2818, 2944] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row77 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (8, 10) xs = true :=
  ⟨([1280, 1282, 1288, 1290, 1408, 1792, 1794, 1800, 1802, 1920, 3328, 3330, 3456, 3840, 3842, 3968, 5376, 5378] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row78 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (8, 11) xs = true :=
  ⟨([2304, 2306, 2336, 2338, 2432, 2464, 2816, 2818, 2944, 3328, 3330, 3456, 3840, 3842, 3968, 6400, 6402, 6528] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row79 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (8, 12) xs = true :=
  ⟨([4352, 4354, 4368, 4370, 4480, 4496, 4864, 4866, 4880, 4882, 4992, 5008, 5376, 5378, 5504, 5888, 5890, 6016] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row80 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (8, 13) xs = true :=
  ⟨([8448, 8456, 8480, 8488, 8576, 8608, 8960, 8968, 9088, 9472, 9480, 9600, 9984, 9992, 10112, 10496, 10528, 10624] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row81 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (9, 10) xs = true :=
  ⟨([1536, 1538, 1540, 1542, 1544, 1546, 1548, 1550, 1664, 1668, 1792, 1794, 1800, 1802, 1920, 3584, 3586, 3588] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row82 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (9, 11) xs = true :=
  ⟨([2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2688, 2689, 2692, 2693, 2816, 2818, 2944, 3584, 3586, 3588] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row83 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (9, 12) xs = true :=
  ⟨([4608, 4609, 4610, 4611, 4624, 4625, 4626, 4627, 4736, 4737, 4752, 4753, 4864, 4866, 4880, 4882, 4992, 5008] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row84 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (9, 13) xs = true :=
  ⟨([8704, 8705, 8712, 8713, 8832, 8833, 8960, 8968, 9088, 9728, 9736, 9856, 9984, 9992, 10112, 10752, 10753, 10880] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row85 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (10, 11) xs = true :=
  ⟨([3072, 3074, 3076, 3078, 3200, 3204, 3328, 3330, 3456, 3584, 3586, 3588, 3590, 3712, 3716, 3840, 3842, 3968] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row86 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (10, 12) xs = true :=
  ⟨([5120, 5122, 5184, 5186, 5248, 5312, 5376, 5378, 5504, 5632, 5634, 5760, 5888, 5890, 6016, 7168, 7170, 7296] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row87 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (10, 13) xs = true :=
  ⟨([9216, 9224, 9280, 9288, 9344, 9408, 9472, 9480, 9600, 9728, 9736, 9856, 9984, 9992, 10112, 11264, 11392, 11520] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row88 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (11, 12) xs = true :=
  ⟨([6144, 6145, 6146, 6147, 6272, 6273, 6400, 6402, 6528, 6656, 6657, 6658, 6659, 6784, 6785, 6912, 6914, 7040] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row89 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (11, 13) xs = true :=
  ⟨([10240, 10241, 10272, 10273, 10368, 10369, 10400, 10401, 10496, 10528, 10624, 10656, 10752, 10753, 10880, 10881, 11008, 11136] : List Input), rfl, by decide +kernel, by decide +kernel⟩
private theorem row90 : ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK (12, 13) xs = true :=
  ⟨([12288, 12289, 12352, 12353, 12416, 12417, 12480, 12481, 12544, 12672, 12800, 12801, 12928, 12929, 13056, 13184, 13312, 13376] : List Input), rfl, by decide +kernel, by decide +kernel⟩
def addEdges : List Edge := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 9), (0, 11), (0, 12), (0, 13), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (2, 10), (2, 11), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (3, 10), (3, 13), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 12), (5, 6), (5, 7), (5, 8), (5, 11), (5, 13), (6, 7), (6, 10), (6, 12), (6, 13), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 10), (9, 11), (9, 12), (9, 13), (10, 11), (10, 12), (10, 13), (11, 12), (11, 13), (12, 13)]
theorem add_cert : ∀ e ∈ addEdges, ∃ xs, xs.length = 18 ∧ xs.Nodup ∧ addOK e xs = true := by
  unfold addEdges
  rw [List.forall_mem_cons]
  refine ⟨row0,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row1,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row2,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row3,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row4,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row5,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row6,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row8,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row10,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row11,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row12,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row13,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row14,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row15,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row16,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row17,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row19,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row20,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row21,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row22,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row23,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row25,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row26,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row27,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row28,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row29,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row31,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row32,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row33,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row36,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row37,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row38,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row40,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row41,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row42,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row45,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row46,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row47,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row48,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row49,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row50,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row53,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row55,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row56,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row57,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row60,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row62,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row63,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row66,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row68,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row69,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row70,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row71,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row72,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row73,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row74,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row75,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row76,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row77,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row78,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row79,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row80,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row81,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row82,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row83,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row84,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row85,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row86,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row87,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row88,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row89,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row90,?_⟩
  simp
def delEdges : List Edge := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
theorem del_cert : ∀ e ∈ delEdges, ∃ xs, xs.length = 47 ∧ xs.Nodup ∧ delOK e xs = true := by
  unfold delEdges
  rw [List.forall_mem_cons]
  refine ⟨row7,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row9,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row18,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row24,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row30,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row34,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row35,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row39,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row43,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row44,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row51,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row52,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row54,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row58,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row59,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row61,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row64,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row65,?_⟩
  rw [List.forall_mem_cons]
  refine ⟨row67,?_⟩
  simp

theorem addition_distance (p : Edge) (hp : p ∈ addEdges) (fs : List Edge) (contains : p ∈ fs) :
    separated 18 fs := by
  obtain ⟨xs,len,nd,v⟩ := add_cert p hp
  refine ⟨xs,len,nd,?_⟩
  intro x hx
  have h := List.all_eq_true.mp v x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have yes : graph fs x = true := List.any_eq_true.mpr ⟨p,contains,h.1⟩
  simp [h.2,yes]

theorem deletion_distance (p : Edge) (hp : p ∈ target) (fs : List Edge)
    (sub : ∀ q ∈ fs, q ∈ target) (missing : p ∉ fs) : separated 47 fs := by
  obtain ⟨xs,len,nd,v⟩ := del_cert p hp
  refine ⟨xs,len,nd,?_⟩
  intro x hx
  have h := List.all_eq_true.mp v x hx
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at h
  have yes : graph target x = true := List.any_eq_true.mpr ⟨p,hp,h.1⟩
  rw [yes]
  intro eq
  obtain ⟨q,hq,value⟩ := List.any_eq_true.mp (show graph fs x = true from eq.symm)
  have ne : q ≠ p := fun e => missing (e ▸ hq)
  have : target.any (fun e => decide (e ≠ p) && hit e x) = true :=
    List.any_eq_true.mpr ⟨q,sub q hq,by simp [ne,value]⟩
  simp_all

theorem all_edits (fs : List Edge) (simple : ∀ q ∈ fs, q ∈ allEdges)
    (different : fs.toFinset ≠ target.toFinset) :
    separated 18 fs ∨ separated 47 fs := by
  by_cases h : ∀ e ∈ fs, e ∈ target
  · right
    have ex : ∃ e ∈ target, e ∉ fs := by
      by_contra! back
      exact different (Finset.ext (fun e => by simpa using Iff.intro (h e) (back e)))
    obtain ⟨e,ht,hf⟩ := ex
    exact deletion_distance e ht fs h hf
  · push Not at h
    obtain ⟨e,hf,ht⟩ := h
    have cover : ∀ e ∈ allEdges, e ∈ target ∨ e ∈ addEdges := by decide +kernel
    exact Or.inl (addition_distance e ((cover e (simple e hf)).resolve_left ht) fs hf)
end PEqualNP.Research.EditRows9811

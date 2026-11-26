import GridPacks
namespace PHPOverlap
def pack687_0 : List Nat := [266, 2058, 596, 652, 785, 674, 1124, 2177, 786, 1292, 2122, 1121, 1290, 1289, 1313, 2184, 2146, 2193, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked687_0 : checkPack 687 false pack687_0 = true := by decide +kernel
def pack687_1 : List Nat := [273, 2065, 610, 2114, 660, 1288, 778, 802, 1297, 1185, 2129, 2130, 2188, 2185, 2186, 2209, 2321, 677, 1130]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked687_1 : checkPack 687 true pack687_1 = true := by decide +kernel
def pack703_0 : List Nat := [273, 652, 660, 673, 674, 1124, 2177, 2184, 2065, 2122, 1297, 2129, 1290, 1289, 1292, 1313, 2130, 2132, 2146, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked703_0 : checkPack 703 false pack703_0 = true := by decide +kernel
def pack703_1 : List Nat := [161, 546, 610, 2114, 2128, 778, 785, 786, 788, 802, 1185, 2185, 2186, 2188, 2193, 2209, 1130, 1137]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked703_1 : checkPack 703 true pack703_1 = true := by decide +kernel
def pack731_0 : List Nat := [273, 2065, 2177, 2184, 676, 788, 802, 1100, 1297, 1121, 1290, 1185, 1289, 2188, 2209, 2321, 2642, 2698, 2705]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked731_0 : checkPack 731 false pack731_0 = true := by decide +kernel
def pack731_1 : List Nat := [610, 778, 2193, 785, 2186, 2130, 1057, 1281, 1288, 1124, 1292, 1313, 2122, 2129, 2185]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked731_1 : checkPack 731 true pack731_1 = true := by decide +kernel
def pack733_0 : List Nat := [273, 610, 778, 660, 2184, 2186, 2130, 2065, 2177, 1121, 1124, 1185, 1289, 1292, 1297, 2122, 2209, 2321, 1825]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked733_0 : checkPack 733 false pack733_0 = true := by decide +kernel
def pack733_1 : List Nat := [266, 2058, 2114, 785, 676, 788, 1313, 1100, 1108, 1288, 1290, 1164, 2129, 2188, 2146, 2185, 2193, 2314, 2642, 2698]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked733_1 : checkPack 733 true pack733_1 = true := by decide +kernel
end PHPOverlap

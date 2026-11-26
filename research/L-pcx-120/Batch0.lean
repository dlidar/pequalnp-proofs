import GridPacks
namespace PHPOverlap
def pack1_0 : List Nat := [266, 2058, 610, 2114, 778, 660, 2184, 2186, 1124, 2130, 1292, 802, 2122, 1108, 1290, 1164, 2188, 2146, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1_0 : checkPack 1 false pack1_0 = true := by decide +kernel
def pack1_1 : List Nat := [273, 785, 2065, 2129, 1185, 2177, 2185, 1297, 1313, 2193, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1_1 : checkPack 1 true pack1_1 = true := by decide +kernel
def pack3_0 : List Nat := [140, 1036, 596, 1092, 652, 660, 2184, 1124, 1292, 1100, 1108, 1164, 2188, 675, 1291, 2131, 2339]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked3_0 : checkPack 3 false pack3_0 = true := by decide +kernel
def pack3_1 : List Nat := [273, 2065, 610, 785, 2186, 2177, 778, 2130, 1313, 2129, 1290, 1185, 2185, 1297, 2122, 2209, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked3_1 : checkPack 3 true pack3_1 = true := by decide +kernel
def pack7_0 : List Nat := [2184, 35, 582, 654, 661, 790, 1102, 1109, 1189, 2189, 2339]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked7_0 : checkPack 7 false pack7_0 = true := by decide +kernel
def pack7_1 : List Nat := [273, 2065, 610, 2177, 778, 2193, 785, 2186, 1124, 2130, 1292, 1313, 2122, 1297, 2129, 1290, 1185, 2185, 2188, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked7_1 : checkPack 7 true pack7_1 = true := by decide +kernel
def pack9_0 : List Nat := [98, 546, 610, 2114, 660, 2128, 674, 1124, 2130, 788, 802, 1108, 1122, 2185, 2132, 2146]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked9_0 : checkPack 9 false pack9_0 = true := by decide +kernel
def pack9_1 : List Nat := [273, 778, 785, 2065, 2122, 2129, 1185, 2177, 2184, 1290, 1292, 1297, 1313, 2186, 2188, 2193, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked9_1 : checkPack 9 true pack9_1 = true := by decide +kernel
end PHPOverlap

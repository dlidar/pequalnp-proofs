import GridPacks
namespace PHPOverlap
def pack27_0 : List Nat := [273, 1092, 1120, 1124, 778, 785, 2130, 2185, 1290, 1297, 2065, 2122, 2129, 2186, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked27_0 : checkPack 27 false pack27_0 = true := by decide +kernel
def pack27_1 : List Nat := [161, 1057, 610, 652, 660, 673, 674, 2177, 2184, 1292, 1313, 1100, 1108, 1121, 1122, 1185, 2188, 2209, 2329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked27_1 : checkPack 27 true pack27_1 = true := by decide +kernel
def pack29_0 : List Nat := [273, 2065, 610, 652, 2193, 1120, 674, 2114, 785, 1292, 802, 1100, 1297, 1122, 1164, 2185, 2129, 2188, 2146, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked29_0 : checkPack 29 false pack29_0 = true := by decide +kernel
def pack29_1 : List Nat := [266, 2177, 673, 1124, 778, 2184, 2130, 2058, 1121, 1185, 1290, 1313, 2122, 2186, 2209, 2314, 1293, 2204]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked29_1 : checkPack 29 true pack29_1 = true := by decide +kernel
def pack31_0 : List Nat := [273, 2065, 596, 778, 2193, 1120, 785, 2130, 1292, 2122, 1297, 1164, 2185, 1290, 2129, 2188, 2186, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked31_0 : checkPack 31 false pack31_0 = true := by decide +kernel
def pack31_1 : List Nat := [161, 1057, 610, 2177, 673, 674, 1124, 2184, 1313, 1121, 1122, 1185, 2209, 668, 790, 1116, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked31_1 : checkPack 31 true pack31_1 = true := by decide +kernel
def pack63_0 : List Nat := [273, 2065, 610, 778, 2193, 785, 2186, 1124, 2130, 1292, 1313, 2122, 1297, 2129, 1290, 1185, 2185, 2188, 2209, 2321, 3136]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked63_0 : checkPack 63 false pack63_0 = true := by decide +kernel
def pack63_1 : List Nat := [2177, 2184, 49, 626, 682, 689, 1196, 1294, 1329, 2140, 2161, 2329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked63_1 : checkPack 63 true pack63_1 = true := by decide +kernel
end PHPOverlap

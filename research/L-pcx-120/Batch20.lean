import GridPacks
namespace PHPOverlap
def pack1775_0 : List Nat := [266, 2058, 610, 652, 785, 674, 1124, 2177, 2130, 788, 1100, 2129, 1122, 1185, 2184, 1297, 2132, 2193, 2314, 1321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1775_0 : checkPack 1775 false pack1775_0 = true := by decide +kernel
def pack1775_1 : List Nat := [273, 2065, 596, 1092, 660, 2128, 778, 1313, 1108, 2185, 1290, 1292, 2122, 2209, 2186, 2188, 2321, 677, 1249]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1775_1 : checkPack 1775 true pack1775_1 = true := by decide +kernel
def pack1791_0 : List Nat := [273, 610, 652, 660, 673, 674, 1124, 2177, 2184, 1100, 1108, 1121, 1122, 1185, 2065, 2321, 790, 1321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1791_0 : checkPack 1791 false pack1791_0 = true := by decide +kernel
def pack1791_1 : List Nat := [161, 1057, 1092, 1120, 778, 785, 2130, 1292, 1313, 2185, 1290, 1297, 2122, 2129, 2188, 2209, 2186, 2193, 1636]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1791_1 : checkPack 1791 true pack1791_1 = true := by decide +kernel
def pack1911_0 : List Nat := [266, 610, 2114, 652, 2184, 785, 786, 788, 1313, 2065, 1297, 1121, 1122, 1124, 1164, 2122, 2193, 2209, 2314, 2187]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1911_0 : checkPack 1911 false pack1911_0 = true := by decide +kernel
def pack1911_1 : List Nat := [273, 2058, 660, 673, 2186, 676, 2177, 778, 1120, 1100, 1185, 2185, 1290, 1292, 2129, 2130, 2188, 2146, 2321, 866]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1911_1 : checkPack 1911 true pack1911_1 = true := by decide +kernel
def pack1919_0 : List Nat := [161, 610, 2114, 2128, 778, 785, 786, 1292, 1313, 1100, 1297, 1121, 1290, 1124, 2185, 2065, 2186, 2188, 2193, 2209]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1919_0 : checkPack 1919 false pack1919_0 = true := by decide +kernel
def pack1919_1 : List Nat := [273, 1057, 652, 660, 673, 674, 676, 2177, 2184, 1185, 2122, 2129, 2130, 2132, 2146, 2321, 852, 1291, 1329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1919_1 : checkPack 1919 true pack1919_1 = true := by decide +kernel
end PHPOverlap

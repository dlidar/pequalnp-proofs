import GridPacks
namespace PHPOverlap
def pack79_0 : List Nat := [266, 610, 778, 784, 2058, 2114, 1108, 2129, 1290, 1124, 1164, 2185, 1292, 2130, 2188, 2146, 2186, 2314, 661]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked79_0 : checkPack 79 false pack79_0 = true := by decide +kernel
def pack79_1 : List Nat := [273, 2065, 2177, 2193, 785, 674, 676, 786, 788, 1313, 2122, 2184, 1185, 1297, 2209, 2321, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked79_1 : checkPack 79 true pack79_1 = true := by decide +kernel
def pack83_0 : List Nat := [273, 610, 2114, 652, 2184, 676, 785, 786, 2065, 1297, 1121, 1122, 1164, 1292, 2122, 2188, 2146, 2193, 2321, 2187]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked83_0 : checkPack 83 false pack83_0 = true := by decide +kernel
def pack83_1 : List Nat := [266, 2058, 660, 673, 2186, 2177, 778, 1120, 788, 1313, 1100, 1124, 1185, 2185, 1290, 2129, 2130, 2209, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked83_1 : checkPack 83 true pack83_1 = true := by decide +kernel
def pack84_0 : List Nat := [266, 2058, 660, 2184, 673, 2186, 2177, 778, 788, 1313, 1100, 1124, 1185, 2185, 1290, 2129, 2130, 2209, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked84_0 : checkPack 84 false pack84_0 = true := by decide +kernel
def pack84_1 : List Nat := [273, 610, 2114, 652, 676, 1120, 785, 786, 2065, 1297, 1121, 1122, 1164, 1292, 2122, 2188, 2146, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked84_1 : checkPack 84 true pack84_1 = true := by decide +kernel
def pack85_0 : List Nat := [273, 2065, 2193, 2184, 2186, 1092, 778, 785, 788, 802, 1100, 1121, 1124, 1290, 1297, 2130, 2321, 1165]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked85_0 : checkPack 85 false pack85_0 = true := by decide +kernel
def pack85_1 : List Nat := [161, 610, 2177, 652, 673, 676, 1120, 786, 1057, 1108, 1122, 1185, 2185, 1292, 1313, 2122, 2129, 2188, 2209]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked85_1 : checkPack 85 true pack85_1 = true := by decide +kernel
end PHPOverlap

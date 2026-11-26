import GridPacks
namespace PHPOverlap
def pack734_0 : List Nat := [266, 2058, 596, 652, 2193, 2184, 785, 2114, 1313, 1290, 1124, 1292, 2129, 2146, 2185, 2314, 1116, 2134]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked734_0 : checkPack 734 false pack734_0 = true := by decide +kernel
def pack734_1 : List Nat := [273, 2065, 610, 2177, 2186, 676, 778, 2130, 788, 2122, 1297, 1288, 1121, 1185, 1289, 2188, 2209, 2321, 2705, 1315]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked734_1 : checkPack 734 true pack734_1 = true := by decide +kernel
def pack735_0 : List Nat := [273, 2065, 596, 652, 660, 2184, 2177, 802, 1121, 1290, 1124, 1185, 1289, 1292, 1297, 2209, 2321, 675, 2252]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked735_0 : checkPack 735 false pack735_0 = true := by decide +kernel
def pack735_1 : List Nat := [140, 1057, 610, 1281, 785, 2186, 676, 778, 2130, 788, 2122, 1108, 1288, 1164, 1313, 2129, 2188, 2185, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked735_1 : checkPack 735 true pack735_1 = true := by decide +kernel
def pack750_0 : List Nat := [273, 2065, 610, 652, 674, 676, 2114, 2130, 1292, 1297, 2184, 1121, 1185, 1290, 2132, 2185, 2209, 2321, 2705]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked750_0 : checkPack 750 false pack750_0 = true := by decide +kernel
def pack750_1 : List Nat := [140, 1057, 596, 2177, 2193, 2128, 785, 778, 1313, 2122, 1122, 1124, 1164, 1289, 2129, 2146, 2186, 2188, 1301, 2323]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked750_1 : checkPack 750 true pack750_1 = true := by decide +kernel
def pack751_0 : List Nat := [266, 2058, 610, 652, 785, 674, 676, 2177, 2130, 1292, 1108, 2184, 1289, 1290, 1313, 2129, 2132, 2193, 2314, 1228]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked751_0 : checkPack 751 false pack751_0 = true := by decide +kernel
def pack751_1 : List Nat := [273, 2065, 596, 1281, 660, 2128, 778, 802, 2122, 1121, 1122, 1124, 1185, 1297, 2209, 2185, 2186, 2188, 2321, 787]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked751_1 : checkPack 751 true pack751_1 = true := by decide +kernel
end PHPOverlap

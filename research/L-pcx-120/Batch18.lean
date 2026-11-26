import GridPacks
namespace PHPOverlap
def pack951_0 : List Nat := [266, 660, 785, 2186, 1124, 2130, 1292, 802, 2065, 1108, 2129, 1290, 1164, 2177, 2185, 2188, 2146, 2314, 2640]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked951_0 : checkPack 951 false pack951_0 = true := by decide +kernel
def pack951_1 : List Nat := [273, 2058, 610, 2114, 778, 2184, 2122, 1185, 1297, 1313, 2193, 2209, 2321, 675, 790, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked951_1 : checkPack 951 true pack951_1 = true := by decide +kernel
def pack959_0 : List Nat := [98, 778, 660, 785, 674, 1124, 2130, 788, 802, 2065, 2122, 1108, 2129, 1122, 2177, 2184, 2132, 2146, 1417]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked959_0 : checkPack 959 false pack959_0 = true := by decide +kernel
def pack959_1 : List Nat := [273, 546, 610, 2114, 2128, 1185, 2185, 1290, 1292, 1297, 1313, 2186, 2188, 2193, 2209, 2321, 677, 794]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked959_1 : checkPack 959 true pack959_1 = true := by decide +kernel
def pack1023_0 : List Nat := [610, 778, 660, 785, 674, 676, 786, 788, 802, 2065, 2177, 2184, 330, 1361, 1417]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1023_0 : checkPack 1023 false pack1023_0 = true := by decide +kernel
def pack1023_1 : List Nat := [273, 546, 770, 784, 2122, 1297, 2129, 1290, 1124, 1185, 2185, 1292, 1313, 2130, 2188, 2209, 2186, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1023_1 : checkPack 1023 true pack1023_1 = true := by decide +kernel
def pack1755_0 : List Nat := [273, 2065, 2177, 2184, 1124, 1292, 1313, 2188, 2209, 2321, 2642, 2698, 2705, 3146, 3153, 3209]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1755_0 : checkPack 1755 false pack1755_0 = true := by decide +kernel
def pack1755_1 : List Nat := [610, 778, 2193, 785, 2186, 2130, 2122, 1297, 2129, 1290, 1185, 2185, 34, 1284, 1312, 2212]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1755_1 : checkPack 1755 true pack1755_1 = true := by decide +kernel
end PHPOverlap

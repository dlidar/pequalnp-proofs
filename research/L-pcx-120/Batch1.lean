import GridPacks
namespace PHPOverlap
def pack10_0 : List Nat := [273, 2065, 596, 2177, 2193, 2128, 785, 1124, 778, 788, 1297, 2129, 1185, 1290, 1313, 2122, 2132, 2186, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked10_0 : checkPack 10 false pack10_0 = true := by decide +kernel
def pack10_1 : List Nat := [140, 1036, 610, 652, 674, 2114, 2130, 802, 1100, 1122, 1164, 2184, 2185, 1292, 2146, 2188]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked10_1 : checkPack 10 true pack10_1 = true := by decide +kernel
def pack11_0 : List Nat := [266, 2058, 596, 1092, 660, 2128, 1124, 778, 788, 1108, 2185, 1290, 2122, 2132, 2186, 2314, 787, 2147]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked11_0 : checkPack 11 false pack11_0 = true := by decide +kernel
def pack11_1 : List Nat := [273, 2065, 610, 652, 785, 674, 2177, 2130, 1313, 1100, 2129, 1122, 1185, 2184, 1292, 1297, 2209, 2188, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked11_1 : checkPack 11 true pack11_1 = true := by decide +kernel
def pack14_0 : List Nat := [273, 778, 2128, 785, 2065, 2122, 2129, 1185, 2177, 1290, 1292, 1297, 1313, 2186, 2188, 2193, 2209, 2321, 598]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked14_0 : checkPack 14 false pack14_0 = true := by decide +kernel
def pack14_1 : List Nat := [98, 546, 610, 2114, 660, 674, 1124, 2130, 788, 802, 1108, 1122, 2184, 2185, 2132, 2146]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked14_1 : checkPack 14 true pack14_1 = true := by decide +kernel
def pack15_0 : List Nat := [266, 778, 2128, 2058, 2122, 1164, 2185, 1290, 1292, 2186, 2188, 2314, 582, 661, 1109]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked15_0 : checkPack 15 false pack15_0 = true := by decide +kernel
def pack15_1 : List Nat := [273, 2065, 610, 2177, 2193, 785, 674, 1124, 2130, 788, 1313, 1297, 2129, 1122, 1185, 2184, 2132, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked15_1 : checkPack 15 true pack15_1 = true := by decide +kernel
end PHPOverlap

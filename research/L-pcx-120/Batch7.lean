import GridPacks
namespace PHPOverlap
def pack219_0 : List Nat := [273, 610, 778, 660, 785, 674, 786, 1100, 1297, 1121, 1290, 1185, 1289, 2065, 2177, 2184, 2188, 2209, 2321, 1828]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked219_0 : checkPack 219 false pack219_0 = true := by decide +kernel
def pack219_1 : List Nat := [1057, 1281, 1288, 1124, 1292, 1313, 2122, 2129, 2130, 2185, 2186, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked219_1 : checkPack 219 true pack219_1 = true := by decide +kernel
def pack221_0 : List Nat := [273, 2065, 2177, 785, 1124, 1292, 802, 1121, 1185, 1289, 1297, 2122, 2184, 2130, 2186, 2209, 2321, 668]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked221_0 : checkPack 221 false pack221_0 = true := by decide +kernel
def pack221_1 : List Nat := [266, 610, 778, 2193, 1288, 674, 786, 2058, 1100, 1108, 1290, 1164, 2114, 1313, 2129, 2188, 2146, 2185, 2314, 677]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked221_1 : checkPack 221 true pack221_1 = true := by decide +kernel
def pack223_0 : List Nat := [273, 2065, 610, 2177, 785, 674, 1124, 778, 786, 1292, 1121, 1290, 1185, 1289, 1297, 2184, 2209, 2321, 2252]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked223_0 : checkPack 223 false pack223_0 = true := by decide +kernel
def pack223_1 : List Nat := [140, 1057, 596, 652, 2193, 1288, 1281, 1313, 2122, 1108, 1164, 2129, 2130, 2188, 2185, 2186, 677, 1294]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked223_1 : checkPack 223 true pack223_1 = true := by decide +kernel
def pack238_0 : List Nat := [273, 2065, 596, 2114, 660, 2184, 785, 778, 802, 1297, 1121, 1185, 1290, 1292, 2130, 2132, 2185, 2209, 2321, 678]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked238_0 : checkPack 238 false pack238_0 = true := by decide +kernel
def pack238_1 : List Nat := [140, 1057, 610, 652, 2186, 1124, 2177, 786, 788, 2122, 1122, 1164, 2128, 1289, 1313, 2129, 2146, 2188, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked238_1 : checkPack 238 true pack238_1 = true := by decide +kernel
end PHPOverlap

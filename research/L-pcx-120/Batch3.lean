import GridPacks
namespace PHPOverlap
def pack73_0 : List Nat := [546, 770, 660, 784, 674, 676, 786, 788, 802, 2122, 2129, 2185]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked73_0 : checkPack 73 false pack73_0 = true := by decide +kernel
def pack73_1 : List Nat := [273, 610, 778, 785, 2065, 2177, 1297, 2184, 1290, 1124, 1185, 1292, 1313, 2130, 2188, 2209, 2186, 2193, 2321, 3145]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked73_1 : checkPack 73 true pack73_1 = true := by decide +kernel
def pack74_0 : List Nat := [273, 2065, 610, 2177, 2193, 784, 785, 676, 778, 788, 1100, 1290, 1185, 1297, 1313, 2130, 2209, 2186, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked74_0 : checkPack 74 false pack74_0 = true := by decide +kernel
def pack74_1 : List Nat := [140, 1036, 596, 652, 674, 1092, 786, 802, 1108, 2184, 2129, 1124, 1164, 2185, 1292, 2122, 2188]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked74_1 : checkPack 74 true pack74_1 = true := by decide +kernel
def pack75_0 : List Nat := [266, 2058, 610, 2114, 660, 784, 676, 778, 788, 1100, 2129, 1290, 2185, 2130, 2146, 2186, 2314, 803]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked75_0 : checkPack 75 false pack75_0 = true := by decide +kernel
def pack75_1 : List Nat := [273, 2065, 596, 652, 785, 674, 2177, 786, 1313, 1297, 2184, 1124, 1185, 1292, 2122, 2188, 2193, 2209, 2321, 1123]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked75_1 : checkPack 75 true pack75_1 = true := by decide +kernel
def pack78_0 : List Nat := [273, 610, 778, 784, 785, 2065, 2177, 1297, 1290, 1124, 1185, 1292, 1313, 2130, 2188, 2209, 2186, 2193, 2321, 3145]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked78_0 : checkPack 78 false pack78_0 = true := by decide +kernel
def pack78_1 : List Nat := [546, 770, 660, 674, 676, 786, 788, 802, 2122, 2184, 2129, 2185]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked78_1 : checkPack 78 true pack78_1 = true := by decide +kernel
end PHPOverlap

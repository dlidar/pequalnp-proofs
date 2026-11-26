import GridPacks
namespace PHPOverlap
def pack95_0 : List Nat := [273, 2065, 610, 778, 2193, 2128, 785, 786, 1292, 2114, 1121, 1290, 1124, 1164, 2185, 1297, 2146, 2186, 2188, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked95_0 : checkPack 95 false pack95_0 = true := by decide +kernel
def pack95_1 : List Nat := [161, 1057, 596, 2177, 673, 674, 676, 2184, 1313, 2122, 1108, 1185, 2129, 2130, 2132, 2209, 668, 1294, 2329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked95_1 : checkPack 95 true pack95_1 = true := by decide +kernel
def pack118_0 : List Nat := [546, 660, 674, 676, 786, 788, 802, 2177, 2122, 2184, 2129, 2185]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked118_0 : checkPack 118 false pack118_0 = true := by decide +kernel
def pack118_1 : List Nat := [273, 610, 770, 778, 784, 785, 2065, 1297, 1290, 1124, 1185, 1292, 1313, 2130, 2188, 2209, 2186, 2193, 2321, 3145]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked118_1 : checkPack 118 true pack118_1 = true := by decide +kernel
def pack119_0 : List Nat := [273, 2065, 2193, 785, 674, 676, 786, 788, 1313, 2114, 2122, 2184, 1185, 1297, 2209, 2321, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked119_0 : checkPack 119 false pack119_0 = true := by decide +kernel
def pack119_1 : List Nat := [266, 610, 2177, 778, 784, 2058, 1108, 2129, 1290, 1124, 1164, 2185, 1292, 2130, 2188, 2146, 2186, 2314, 689]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked119_1 : checkPack 119 true pack119_1 = true := by decide +kernel
def pack127_0 : List Nat := [273, 2065, 778, 2193, 785, 2186, 676, 786, 1292, 1313, 2114, 2128, 1185, 2185, 1290, 1297, 2188, 2209, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked127_0 : checkPack 127 false pack127_0 = true := by decide +kernel
def pack127_1 : List Nat := [98, 610, 2177, 2184, 2122, 1108, 2129, 1122, 1124, 2130, 2132, 2146, 554, 689, 1193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked127_1 : checkPack 127 true pack127_1 = true := by decide +kernel
end PHPOverlap

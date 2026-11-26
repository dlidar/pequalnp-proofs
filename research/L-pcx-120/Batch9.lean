import GridPacks
namespace PHPOverlap
def pack586_0 : List Nat := [273, 2065, 596, 652, 2186, 2177, 2130, 1313, 1100, 1290, 1185, 1297, 2209, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked586_0 : checkPack 586 false pack586_0 = true := by decide +kernel
def pack586_1 : List Nat := [140, 1036, 610, 1092, 660, 2184, 785, 1124, 778, 1292, 1108, 2129, 1164, 2185, 2122, 2188, 1315, 2211, 2323]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked586_1 : checkPack 586 true pack586_1 = true := by decide +kernel
def pack587_0 : List Nat := [266, 2058, 596, 652, 785, 2186, 2114, 2130, 802, 1100, 2129, 1290, 2185, 2146, 2314, 1184, 1300, 2196]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked587_0 : checkPack 587 false pack587_0 = true := by decide +kernel
def pack587_1 : List Nat := [273, 2065, 610, 2177, 2193, 2184, 1124, 778, 1292, 1297, 1185, 1313, 2122, 2188, 2209, 2321, 675, 1291, 2131]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked587_1 : checkPack 587 true pack587_1 = true := by decide +kernel
def pack590_0 : List Nat := [273, 2065, 2177, 2193, 2186, 1124, 2130, 1292, 1313, 1297, 1290, 1185, 2188, 2209, 2321, 2640, 2697]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked590_0 : checkPack 590 false pack590_0 = true := by decide +kernel
def pack590_1 : List Nat := [610, 778, 2184, 785, 2122, 2129, 2185, 35, 2179, 1189, 1301, 1315, 2197, 2323]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked590_1 : checkPack 590 true pack590_1 = true := by decide +kernel
def pack591_0 : List Nat := [266, 2058, 2114, 660, 785, 2186, 1124, 2130, 1292, 802, 1108, 2129, 1290, 1164, 2185, 2188, 2146, 2314, 2640]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked591_0 : checkPack 591 false pack591_0 = true := by decide +kernel
def pack591_1 : List Nat := [273, 610, 778, 2184, 2065, 2122, 1185, 2177, 1297, 1313, 2193, 2209, 2321, 675, 790, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked591_1 : checkPack 591 true pack591_1 = true := by decide +kernel
end PHPOverlap

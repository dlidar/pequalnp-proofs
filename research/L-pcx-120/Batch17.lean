import GridPacks
namespace PHPOverlap
def pack758_0 : List Nat := [161, 610, 2193, 2186, 676, 2114, 778, 2128, 785, 2122, 2129, 1185, 1289, 2188, 2209, 2074, 1294, 1329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked758_0 : checkPack 758 false pack758_0 = true := by decide +kernel
def pack758_1 : List Nat := [273, 2065, 2177, 652, 2184, 673, 2130, 1292, 1313, 1297, 1290, 1124, 2132, 2146, 2185, 2321, 724, 1249, 2250]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked758_1 : checkPack 758 true pack758_1 = true := by decide +kernel
def pack759_0 : List Nat := [273, 610, 660, 673, 2186, 676, 2177, 778, 2128, 2065, 2122, 1164, 1297, 1313, 2185, 2188, 2321, 790, 1123]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked759_0 : checkPack 759 false pack759_0 = true := by decide +kernel
def pack759_1 : List Nat := [266, 2058, 1281, 652, 2184, 785, 2130, 1292, 802, 1108, 2129, 1290, 1124, 1185, 1289, 2132, 2209, 2193, 2314, 738]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked759_1 : checkPack 759 true pack759_1 = true := by decide +kernel
def pack767_0 : List Nat := [273, 610, 652, 660, 673, 674, 676, 2177, 2184, 2065, 1289, 1290, 1292, 1297, 1313, 2321, 1228, 2133, 2162]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked767_0 : checkPack 767 false pack767_0 = true := by decide +kernel
def pack767_1 : List Nat := [161, 546, 1281, 1288, 778, 785, 2130, 788, 802, 2122, 1108, 2129, 1122, 1124, 1185, 2188, 2209, 2185, 2186, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked767_1 : checkPack 767 true pack767_1 = true := by decide +kernel
def pack950_0 : List Nat := [273, 2193, 2186, 1124, 2130, 1292, 1313, 1297, 1290, 1185, 2188, 2209, 2321, 2570, 2640, 2689, 3145]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked950_0 : checkPack 950 false pack950_0 = true := by decide +kernel
def pack950_1 : List Nat := [2065, 610, 2177, 778, 2184, 785, 2122, 2129, 2185, 338, 1126, 1364, 1441, 2190, 2225]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked950_1 : checkPack 950 true pack950_1 = true := by decide +kernel
end PHPOverlap

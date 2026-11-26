import GridPacks
namespace PHPOverlap
def pack1757_0 : List Nat := [273, 610, 778, 660, 2184, 2186, 2130, 2065, 2122, 1108, 1290, 1164, 2177, 1313, 2209, 2321, 677, 1293, 2133]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1757_0 : checkPack 1757 false pack1757_0 = true := by decide +kernel
def pack1757_1 : List Nat := [266, 2058, 2114, 785, 1124, 1292, 802, 2129, 1185, 2185, 1297, 2188, 2146, 2193, 2314, 2640, 2698, 3146]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1757_1 : checkPack 1757 true pack1757_1 = true := by decide +kernel
def pack1759_0 : List Nat := [273, 2065, 596, 652, 660, 2184, 2177, 1313, 1100, 1108, 1164, 2209, 2321, 675, 790, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1759_0 : checkPack 1759 false pack1759_0 = true := by decide +kernel
def pack1759_1 : List Nat := [140, 1036, 610, 1092, 785, 2186, 1124, 778, 2130, 1292, 2129, 1290, 1185, 2185, 1297, 2122, 2188, 2193, 1312]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1759_1 : checkPack 1759 true pack1759_1 = true := by decide +kernel
def pack1773_0 : List Nat := [98, 546, 778, 785, 1124, 788, 802, 2122, 2129, 1185, 2177, 2184, 1290, 1297, 2132, 2146, 2186, 2193, 2642, 2329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1773_0 : checkPack 1773 false pack1773_0 = true := by decide +kernel
def pack1773_1 : List Nat := [273, 610, 2114, 660, 2128, 674, 2130, 2065, 1108, 1122, 2185, 1292, 1313, 2188, 2209, 2321, 677, 1228]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1773_1 : checkPack 1773 true pack1773_1 = true := by decide +kernel
def pack1774_0 : List Nat := [273, 2065, 610, 652, 674, 1124, 2114, 2130, 788, 1100, 1122, 1164, 2184, 2185, 1313, 2132, 2209, 2321, 2705, 3153]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1774_0 : checkPack 1774 false pack1774_0 = true := by decide +kernel
def pack1774_1 : List Nat := [140, 1036, 596, 2177, 2193, 2128, 785, 778, 802, 1297, 2129, 1185, 1290, 1292, 2122, 2146, 2186, 2188, 2329]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked1774_1 : checkPack 1774 true pack1774_1 = true := by decide +kernel
end PHPOverlap

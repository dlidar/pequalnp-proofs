import GridPacks
namespace PHPOverlap
def pack639_0 : List Nat := [273, 610, 2114, 2128, 2065, 1185, 2185, 1290, 1292, 1297, 1313, 2186, 2188, 2193, 2209, 2321, 677, 794]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked639_0 : checkPack 639 false pack639_0 = true := by decide +kernel
def pack639_1 : List Nat := [98, 546, 778, 660, 785, 674, 1124, 2130, 788, 802, 2122, 1108, 2129, 1122, 2177, 2184, 2132, 2146, 1193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked639_1 : checkPack 639 true pack639_1 = true := by decide +kernel
def pack667_0 : List Nat := [273, 2065, 610, 2177, 2184, 1124, 788, 802, 1185, 1289, 1290, 1297, 2122, 2129, 2130, 2188, 2209, 2321, 2698, 2705]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked667_0 : checkPack 667 false pack667_0 = true := by decide +kernel
def pack667_1 : List Nat := [98, 778, 2193, 785, 2186, 786, 1057, 1100, 1108, 1121, 1122, 2114, 2128, 1292, 1313, 2132, 2146, 2185, 1636]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked667_1 : checkPack 667 true pack667_1 = true := by decide +kernel
def pack668_0 : List Nat := [98, 778, 2193, 2184, 785, 2186, 786, 1057, 1100, 1108, 1121, 1122, 2114, 1292, 1313, 2132, 2146, 2185, 1636]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked668_0 : checkPack 668 false pack668_0 = true := by decide +kernel
def pack668_1 : List Nat := [273, 2065, 610, 2177, 1124, 788, 802, 1185, 2128, 1289, 1290, 1297, 2122, 2129, 2130, 2188, 2209, 2321, 2698, 2705]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked668_1 : checkPack 668 true pack668_1 = true := by decide +kernel
def pack669_0 : List Nat := [273, 778, 660, 2184, 2186, 786, 2065, 1100, 1297, 1122, 1185, 1289, 1292, 2177, 2129, 2132, 2209, 2321, 1636, 1825]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked669_0 : checkPack 669 false pack669_0 = true := by decide +kernel
def pack669_1 : List Nat := [266, 2058, 610, 1281, 785, 1124, 788, 1313, 1121, 1164, 2128, 1290, 2122, 2130, 2185, 2188, 2193, 2314, 2698]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked669_1 : checkPack 669 true pack669_1 = true := by decide +kernel
end PHPOverlap

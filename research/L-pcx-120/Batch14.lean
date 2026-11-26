import GridPacks
namespace PHPOverlap
def pack671_0 : List Nat := [273, 2065, 610, 652, 660, 2184, 2177, 802, 2122, 1297, 1185, 1289, 1290, 1292, 2129, 2130, 2132, 2209, 2321, 675]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked671_0 : checkPack 671 false pack671_0 = true := by decide +kernel
def pack671_1 : List Nat := [140, 1057, 596, 2114, 785, 2186, 1124, 778, 786, 788, 1121, 1122, 1164, 2128, 1313, 2146, 2185, 2188, 2193, 1116]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked671_1 : checkPack 671 true pack671_1 = true := by decide +kernel
def pack679_0 : List Nat := [140, 1057, 596, 785, 2186, 1124, 2177, 778, 786, 788, 1121, 1122, 1164, 2128, 1313, 2146, 2185, 2188, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked679_0 : checkPack 679 false pack679_0 = true := by decide +kernel
def pack679_1 : List Nat := [273, 2065, 610, 2114, 652, 660, 2184, 802, 2122, 1297, 1185, 1289, 1290, 1292, 2129, 2130, 2132, 2209, 2321, 675]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked679_1 : checkPack 679 true pack679_1 = true := by decide +kernel
def pack685_0 : List Nat := [1057, 610, 778, 785, 1124, 1292, 1313, 1100, 1121, 1289, 2177, 2184, 2130, 2186, 2193]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked685_0 : checkPack 685 false pack685_0 = true := by decide +kernel
def pack685_1 : List Nat := [273, 1281, 660, 1288, 674, 786, 1297, 1290, 1185, 2065, 2122, 2129, 2188, 2209, 2185, 2321, 1636, 1804, 1825]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked685_1 : checkPack 685 true pack685_1 = true := by decide +kernel
def pack686_0 : List Nat := [273, 2065, 596, 652, 674, 1124, 1281, 786, 1292, 2122, 1290, 1185, 1297, 2184, 2129, 2209, 2185, 2321, 1825, 2260]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked686_0 : checkPack 686 false pack686_0 = true := by decide +kernel
def pack686_1 : List Nat := [140, 1057, 610, 2177, 2193, 1288, 785, 778, 1313, 1108, 1121, 1164, 1289, 2130, 2188, 2186, 1126, 2154]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked686_1 : checkPack 686 true pack686_1 = true := by decide +kernel
end PHPOverlap

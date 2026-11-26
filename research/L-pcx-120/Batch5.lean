import GridPacks
namespace PHPOverlap
def pack87_0 : List Nat := [273, 2065, 610, 2193, 2184, 785, 786, 788, 2114, 2122, 1121, 1122, 1124, 1297, 2146, 2321, 654, 1165]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked87_0 : checkPack 87 false pack87_0 = true := by decide +kernel
def pack87_1 : List Nat := [266, 2058, 596, 2177, 778, 673, 2186, 676, 1120, 1313, 1108, 1185, 2185, 1290, 1292, 2129, 2130, 2188, 2209, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked87_1 : checkPack 87 true pack87_1 = true := by decide +kernel
def pack91_0 : List Nat := [273, 610, 2114, 2128, 676, 778, 785, 786, 1100, 1297, 1121, 1290, 2185, 2065, 2132, 2146, 2186, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked91_0 : checkPack 91 false pack91_0 = true := by decide +kernel
def pack91_1 : List Nat := [161, 1057, 652, 660, 673, 674, 2177, 2184, 1292, 1313, 1124, 1185, 2122, 2129, 2130, 2188, 2209, 1291]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked91_1 : checkPack 91 true pack91_1 = true := by decide +kernel
def pack93_0 : List Nat := [273, 2065, 652, 2193, 2128, 674, 1092, 785, 1292, 802, 1121, 1124, 1164, 2185, 1297, 2122, 2130, 2188, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked93_0 : checkPack 93 false pack93_0 = true := by decide +kernel
def pack93_1 : List Nat := [266, 610, 2177, 673, 676, 778, 2184, 786, 2058, 1100, 1108, 1290, 1185, 1313, 2129, 2132, 2209, 2186, 2314, 1293]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked93_1 : checkPack 93 true pack93_1 = true := by decide +kernel
def pack94_0 : List Nat := [266, 2058, 610, 778, 660, 2128, 673, 786, 1292, 2177, 1290, 1124, 1185, 1313, 2129, 2209, 2186, 2188, 2314, 1116]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked94_0 : checkPack 94 false pack94_0 = true := by decide +kernel
def pack94_1 : List Nat := [273, 2065, 596, 770, 674, 676, 2184, 785, 802, 2122, 1297, 1121, 2185, 2130, 2132, 2193, 2321, 796]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked94_1 : checkPack 94 true pack94_1 = true := by decide +kernel
end PHPOverlap

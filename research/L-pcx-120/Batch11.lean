import GridPacks
namespace PHPOverlap
def pack598_0 : List Nat := [161, 1057, 596, 2177, 778, 674, 1124, 2184, 785, 1313, 2122, 1122, 1185, 2185, 2129, 2209, 1308, 2204, 2330]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked598_0 : checkPack 598 false pack598_0 = true := by decide +kernel
def pack598_1 : List Nat := [273, 2065, 610, 2193, 1120, 673, 2130, 1292, 1297, 1121, 1164, 1290, 2188, 2186, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked598_1 : checkPack 598 true pack598_1 = true := by decide +kernel
def pack599_0 : List Nat := [273, 2065, 596, 2114, 778, 673, 674, 1124, 2184, 802, 2122, 1121, 1122, 1297, 2146, 2193, 2321, 790, 1165]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked599_0 : checkPack 599 false pack599_0 = true := by decide +kernel
def pack599_1 : List Nat := [266, 2058, 610, 660, 1120, 785, 2130, 1292, 1108, 1185, 2177, 2185, 1290, 1313, 2129, 2188, 2186, 2209, 2314]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked599_1 : checkPack 599 true pack599_1 = true := by decide +kernel
def pack603_0 : List Nat := [273, 2065, 652, 2193, 673, 2186, 2114, 2128, 788, 802, 1100, 1297, 1121, 1290, 2185, 2132, 2146, 2321, 2642, 1188]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked603_0 : checkPack 603 false pack603_0 = true := by decide +kernel
def pack603_1 : List Nat := [161, 610, 2177, 2184, 1124, 778, 785, 2130, 1057, 1185, 1292, 1313, 2122, 2129, 2188, 2209, 1291]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked603_1 : checkPack 603 true pack603_1 = true := by decide +kernel
def pack605_0 : List Nat := [273, 610, 1092, 673, 1124, 778, 2128, 2130, 2065, 1121, 1164, 2185, 1292, 1297, 2122, 2188, 2193, 2321, 1314, 2210]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked605_0 : checkPack 605 false pack605_0 = true := by decide +kernel
def pack605_1 : List Nat := [266, 2058, 652, 660, 2184, 2186, 2177, 785, 788, 1313, 1100, 1108, 1290, 1185, 2129, 2132, 2209, 2314, 2642]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked605_1 : checkPack 605 true pack605_1 = true := by decide +kernel
end PHPOverlap

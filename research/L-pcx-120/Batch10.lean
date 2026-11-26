import GridPacks
namespace PHPOverlap
def pack594_0 : List Nat := [161, 1057, 660, 674, 2177, 778, 2184, 785, 1292, 1313, 1108, 1122, 1185, 2185, 2122, 2129, 2188, 2209, 1636, 2330]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked594_0 : checkPack 594 false pack594_0 = true := by decide +kernel
def pack594_1 : List Nat := [273, 610, 1092, 652, 1120, 673, 1124, 2130, 1100, 1121, 1290, 1297, 2065, 2186, 2193, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked594_1 : checkPack 594 true pack594_1 = true := by decide +kernel
def pack595_0 : List Nat := [273, 2065, 2193, 673, 674, 2114, 778, 2184, 1292, 802, 1297, 1121, 1122, 1164, 2122, 2188, 2146, 2321, 2642]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked595_0 : checkPack 595 false pack595_0 = true := by decide +kernel
def pack595_1 : List Nat := [266, 610, 2177, 652, 1120, 1124, 785, 2130, 2058, 1100, 1185, 2185, 1290, 1313, 2129, 2186, 2209, 2314, 1308, 2204]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked595_1 : checkPack 595 true pack595_1 = true := by decide +kernel
def pack596_0 : List Nat := [266, 610, 2177, 652, 1124, 2184, 785, 2130, 2058, 1100, 1185, 2185, 1290, 1313, 2129, 2186, 2209, 2314, 1308, 2204]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked596_0 : checkPack 596 false pack596_0 = true := by decide +kernel
def pack596_1 : List Nat := [273, 2065, 2193, 1120, 673, 674, 2114, 778, 1292, 802, 1297, 1121, 1122, 1164, 2122, 2188, 2146, 2321, 2642]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked596_1 : checkPack 596 true pack596_1 = true := by decide +kernel
def pack597_0 : List Nat := [273, 610, 1092, 652, 673, 1124, 2184, 2130, 1100, 1121, 1290, 1297, 2065, 2186, 2193, 2321, 1165]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked597_0 : checkPack 597 false pack597_0 = true := by decide +kernel
def pack597_1 : List Nat := [161, 1057, 660, 1120, 674, 2177, 778, 785, 1292, 1313, 1108, 1122, 1185, 2185, 2122, 2129, 2188, 2209, 1636, 2330]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked597_1 : checkPack 597 true pack597_1 = true := by decide +kernel
end PHPOverlap

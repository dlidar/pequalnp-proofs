import GridPacks
namespace PHPOverlap
def pack606_0 : List Nat := [266, 2058, 596, 2177, 2186, 1124, 2128, 785, 1313, 1290, 1185, 1292, 2129, 2209, 2188, 2314, 668, 1305, 2138]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked606_0 : checkPack 606 false pack606_0 = true := by decide +kernel
def pack606_1 : List Nat := [273, 2065, 610, 778, 2193, 2184, 673, 2130, 788, 2122, 1297, 1121, 2185, 2132, 2321, 2179, 1189, 1315]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked606_1 : checkPack 606 true pack606_1 = true := by decide +kernel
def pack607_0 : List Nat := [273, 2065, 596, 2114, 673, 2186, 1124, 2128, 802, 1121, 1290, 1164, 2185, 1292, 1297, 2146, 2188, 2193, 2321, 794]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked607_0 : checkPack 607 false pack607_0 = true := by decide +kernel
def pack607_1 : List Nat := [161, 1057, 610, 778, 660, 2184, 785, 2130, 788, 2122, 1108, 1185, 2177, 1313, 2129, 2132, 2209, 678, 1291]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked607_1 : checkPack 607 true pack607_1 = true := by decide +kernel
def pack630_0 : List Nat := [610, 2177, 778, 2184, 785, 2122, 2129, 2185, 49, 1196, 1294, 1329, 2190, 2225, 2330]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked630_0 : checkPack 630 false pack630_0 = true := by decide +kernel
def pack630_1 : List Nat := [273, 2065, 2193, 2186, 1124, 2130, 1292, 1313, 1297, 1290, 1185, 2188, 2209, 2321, 2626, 2696, 3145]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked630_1 : checkPack 630 true pack630_1 = true := by decide +kernel
def pack631_0 : List Nat := [273, 610, 2114, 778, 2184, 2065, 2122, 1185, 1297, 1313, 2193, 2209, 2321, 675, 790, 1123, 2189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked631_0 : checkPack 631 false pack631_0 = true := by decide +kernel
def pack631_1 : List Nat := [266, 2058, 660, 785, 2186, 1124, 2130, 1292, 802, 1108, 2129, 1290, 1164, 2177, 2185, 2188, 2146, 2314, 2640]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked631_1 : checkPack 631 true pack631_1 = true := by decide +kernel
end PHPOverlap

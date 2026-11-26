import GridPacks
namespace PHPOverlap
def pack2047_0 : List Nat := [610, 778, 660, 785, 674, 1124, 786, 1292, 1313, 1100, 1297, 1121, 1290, 1185, 1289, 2065, 2177, 2184]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked2047_0 : checkPack 2047 false pack2047_0 = true := by decide +kernel
def pack2047_1 : List Nat := [273, 1057, 1281, 1288, 2122, 2129, 2130, 2188, 2209, 2185, 2186, 2193, 2321, 1636, 1804, 1826, 1697]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked2047_1 : checkPack 2047 true pack2047_1 = true := by decide +kernel
def pack4095_0 : List Nat := [610, 778, 2193, 785, 2186, 1124, 2130, 1292, 1313, 2122, 1297, 2129, 1290, 1185, 2185, 2188, 2209, 2321, 34, 2176]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked4095_0 : checkPack 4095 false pack4095_0 = true := by decide +kernel
def pack4095_1 : List Nat := [273, 2065, 2177, 2184, 2642, 2698, 2705, 1125, 1293, 1826, 3148, 3233, 3345]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked4095_1 : checkPack 4095 true pack4095_1 = true := by decide +kernel
end PHPOverlap

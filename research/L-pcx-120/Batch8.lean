import GridPacks
namespace PHPOverlap
def pack239_0 : List Nat := [266, 2058, 596, 2177, 2193, 2184, 778, 1313, 1108, 1289, 1290, 1292, 2129, 2130, 2132, 2314, 675, 1252, 2154]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked239_0 : checkPack 239 false pack239_0 = true := by decide +kernel
def pack239_1 : List Nat := [273, 2065, 610, 652, 785, 2186, 1124, 1281, 786, 788, 2122, 1121, 1122, 1185, 2128, 1297, 2209, 2185, 2188, 2321]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked239_1 : checkPack 239 true pack239_1 = true := by decide +kernel
def pack255_0 : List Nat := [273, 2065, 2177, 2184, 778, 785, 786, 1292, 1313, 1289, 1290, 1297, 2321, 740, 1228, 2133, 2274]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked255_0 : checkPack 255 false pack255_0 = true := by decide +kernel
def pack255_1 : List Nat := [161, 610, 652, 2193, 673, 2186, 1124, 1281, 1288, 2122, 1108, 2129, 1122, 1185, 2130, 2188, 2209, 2185]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked255_1 : checkPack 255 true pack255_1 = true := by decide +kernel
def pack511_0 : List Nat := [2065, 2177, 2184, 330, 850, 906, 913, 1361, 1126, 1420, 2189, 2465]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked511_0 : checkPack 511 false pack511_0 = true := by decide +kernel
def pack511_1 : List Nat := [273, 610, 778, 2193, 785, 2186, 1124, 2130, 1292, 1313, 2122, 1297, 2129, 1290, 1185, 2185, 2188, 2209, 2321, 3073]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked511_1 : checkPack 511 true pack511_1 = true := by decide +kernel
def pack585_0 : List Nat := [610, 778, 785, 2122, 2129, 2185, 34, 1188, 2176, 1300, 1314, 2196, 2210, 2322]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked585_0 : checkPack 585 false pack585_0 = true := by decide +kernel
def pack585_1 : List Nat := [273, 2065, 2177, 2193, 2184, 2186, 1124, 2130, 1292, 1313, 1297, 1290, 1185, 2188, 2209, 2321, 2634]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked585_1 : checkPack 585 true pack585_1 = true := by decide +kernel
end PHPOverlap

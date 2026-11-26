import Core
namespace PEqualNP.Outside.Mask1534
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem br0 : optimized 7 1 [0xfc0000fffffffc1041041041041, 0x3fffffc0000002082082082082, 0xfc000000000003cf3cf3cf3cf3c, 0x3f000000fc4104104104104, 0xfc000003f008208208208208, 0x3f000000fc0010410410410410, 0x3f0000228a28a28a28a2] = false := by decide +kernel
end PEqualNP.Outside.Mask1534

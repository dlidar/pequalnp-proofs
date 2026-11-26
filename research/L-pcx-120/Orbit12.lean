import OrbitData
namespace PHPOverlap
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem orb12 : ∀ k : Fin 256, rightEntry (3072+k.val) = true := by decide +kernel
end PHPOverlap

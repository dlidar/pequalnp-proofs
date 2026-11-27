import Groups
namespace PEqualNP.Outside.Comparator9929
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem coverage : ∀ t : Fin 13, rawInputs.sublists.all (fun ws => decide (12 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top) || allRoots.contains (t.val, ws)) = true := by decide +kernel
end PEqualNP.Outside.Comparator9929

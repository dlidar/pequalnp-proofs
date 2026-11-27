import Groups
namespace PEqualNP.Outside.Mask4294973
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem coverage : ∀ t : Fin 11, rawInputs.sublists.all (fun ws => decide (10 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top) || allRoots.contains (t.val, ws)) = true := by decide +kernel
end PEqualNP.Outside.Mask4294973

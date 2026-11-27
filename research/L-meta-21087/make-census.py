from pathlib import Path
import json,sys
p=Path(__file__).resolve().parent
sys.path.insert(0,str(p));sys.argv=['profiles.py','8']
from profiles import raw,roots,width,top
d=p/'unrestricted';ns='PEqualNP.Outside.Mask114591'
fmt=lambda ws:'['+', '.join(f'({x>>width},{x&top})' for x in ws)+']'
def prof(t,ws):return f'({t}, {fmt(ws)})'
good=[(a['inverters'],tuple(raw[j] for j in a['inputs'])) for a in json.loads((p/'profiles.json').read_text())]
bad=[a for a in roots() if a not in good];parts=[bad[j:j+3] for j in range(0,len(bad),3)]
s=f'import Lower\nnamespace {ns}\n'
s+='def listedProfiles : List (Nat × List Sig) := ['+', '.join(prof(*z) for z in good)+']\n'
for i,group in enumerate(parts):s+=f'def testGroup{i} : List (Nat × List Sig) := ['+', '.join(prof(*z) for z in group)+']\n'
s+='def excludedGroups := '+' ++ '.join(f'testGroup{i}' for i in range(len(parts)))+'\n'
s+='''set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem coversProfiles : ∀ t : Fin 10, rawInputs.sublists.all (fun ws =>
    decide (9 < ws.length + t.val) || (cuts (decide (0 < t.val)) ws != top) || listedProfiles.contains (t.val,ws) || excludedGroups.contains (t.val,ws)) = true := by decide +kernel
'''
(d/'ProfileGroups.lean').write_text(s+f'end {ns}\n')
for i,group in enumerate(parts):
 (d/f'TestGroup{i}.lean').write_text(f'import ProfileGroups\nnamespace {ns}\nset_option maxRecDepth 60000 in\nset_option maxHeartbeats 0 in\ntheorem rejectedGroup{i} : testGroup{i}.all (fun z => !(search 8 z.1 z.2)) = true := by decide +kernel\nend {ns}\n')
s=''.join(f'import TestGroup{i}\n' for i in range(len(parts)))+f'namespace {ns}\n'
s+='theorem allExcluded : excludedGroups.all (fun z => !(search 8 z.1 z.2)) = true := by\n  simp only [excludedGroups, List.all_append, '+', '.join(f'rejectedGroup{i}' for i in range(len(parts)))+', Bool.and_self]\n'
s+='''theorem normalized_profile {t : Nat} {S : Finset Sig} (sub : S ⊆ rawInputs.toFinset) (hl : live 8 t S) :
    (t,rawInputs.filter (fun a => decide (a ∈ S))) ∈ listedProfiles := by
  let l := rawInputs.filter (fun a => decide (a ∈ S))
  have eq : l.toFinset = S := by
    ext a
    simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (sub h),h⟩⟩
  have nd : l.Nodup := (by decide : rawInputs.Nodup).filter _
  have hv : ∀ a ∈ l, valid a := fun a ha => rawInputs_valid a (List.mem_filter.mp ha).1
  have lin : live 8 t l.toFinset := eq ▸ hl
  have hc := live_card lin
  rw [List.toFinset_card_of_nodup nd] at hc
  have hsep := cuts_full hv lin
  have hit := search_complete 8 t l nd hv lin
  have row := List.all_eq_true.mp (coversProfiles ⟨t,by omega⟩) l (List.mem_sublists.mpr List.filter_sublist)
  by_contra hn
  have ng : listedProfiles.contains (t,l) = false := by simpa [l] using hn
  have mem : (t,l) ∈ excludedGroups := by
    exact (show (t,l) ∈ listedProfiles ∨ (t,l) ∈ excludedGroups by simpa [show ¬ 9 < l.length + t by omega,hsep] using row).resolve_left hn
  have nog := List.all_eq_true.mp allExcluded (t,l) mem
  simp [hit] at nog
'''
(d/'ProfileCensus.lean').write_text(s+f'end {ns}\n#print axioms {ns}.normalized_profile\n')
print(len(parts),'groups for',len(bad),'excluded profiles')

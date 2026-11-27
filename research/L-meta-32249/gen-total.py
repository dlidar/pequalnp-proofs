from cutwidth import *
D=json.loads((p/'cutwidth.json').read_text());ts=[t for t in range(256) if t.bit_count()==4 and t<255^t]
def vec(x):return '!['+','.join(map(str,x))+']'
out=['import Both']+['import Cut'+str(t) for t in sorted(ts+[255^t for t in ts])]+['namespace Graph32249.Balanced','open MonotoneCut','set_option maxRecDepth 18000','set_option maxHeartbeats 4000000']
for t in ts:
 u=t^255;k=D[str(t)]['width']+D[str(u)]['width']
 out+=[f'theorem swap{t} : (fun b a => Cut{t}.eval a b) = Cut{u}.eval := by',
 '  funext b a','  apply congrArg target;funext i;fin_cases i <;> rfl',
 f'theorem sum{t} (n : Nat) : BothCan Cut{t}.eval n ↔ {k} ≤ n := by',
 f'  exact add_widths Cut{t}.exact_width (by rw [swap{t}];exact Cut{u}.exact_width) n']
out+=['def masks : Fin 35 → Nat := '+vec(ts),'def graph : Fin 35 → Four → Four → Bool := '+vec('Cut'+str(t)+'.eval' for t in ts),'def widths : Fin 35 → Nat := '+vec(D[str(t)]['width']+D[str(255^t)]['width'] for t in ts),
 'theorem minimum (i : Fin 35) (n : Nat) : BothCan (graph i) n ↔ widths i ≤ n := by','  fin_cases i']+['  · exact sum'+str(t)+' n' for t in ts]
out+=['theorem five_bits (i : Fin 35) : BothCan (graph i) 5 ↔ masks i=83 ∨ masks i=86 := by',
'  rw [minimum]','  exact (show ∀ j : Fin 35,widths j ≤ 5 ↔ masks j=83 ∨ masks j=86 by decide +kernel) i',
'theorem histogram : (List.ofFn widths).count 5=2 ∧ (List.ofFn widths).count 6=12 ∧ (List.ofFn widths).count 7=11 ∧ (List.ofFn widths).count 8=10 := by decide +kernel',
'end Graph32249.Balanced']
(p/'Total.lean').write_text('\n'.join(out)+'\n')

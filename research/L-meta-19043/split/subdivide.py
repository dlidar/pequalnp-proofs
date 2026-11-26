"""Refine expensive kernel checks using certified exclusions of first-step states."""
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json
from search import children, roots, K, width, top

d=Path(__file__).resolve().parent
out=d/'parts'
out.mkdir(exist_ok=True)
namespace='PEqualNP.Outside.Mask5805'
limit=4000
module_budget=14000
@lru_cache(maxsize=700000)
def cost(k,t,ordered):
    if not k: return 1
    return 1 + sum(cost(k-1,u,tuple(sorted(ch))) for u,ch,_ in children(k,t,ordered))

def literal(t,ws):
    return '('+str(t)+', ['+', '.join(f'({hex(v>>width)}, {hex(v&top)})' for v in ws)+'])'

records=[]
index={}
def node(k,t,ws):
    key=k,t,ws
    if key in index:return index[key]
    charge=cost(k,t,tuple(sorted(ws)))
    chosen=[]
    if charge>limit:
        mult=Counter((u,ch) for u,ch,_ in children(k,t,ws))
        sizes=sorted(((m*cost(k-1,u,tuple(sorted(ch))),u,ch) for (u,ch),m in mult.items()),reverse=True)
        for c,u,ch in sizes:
            chosen.append(node(k-1,u,ch))
            charge-=c
            if charge<=limit:break
    tag=len(records)
    records.append((k,t,ws,chosen,charge));index[key]=tag
    return tag
root_ids=[node(K,t,ws) for t,ws in roots()]
modules=[];active=[];used=0
for n,record in enumerate(records):
    c=record[-1]
    if active and used+c>module_budget:
        modules.append(active);active=[];used=0
    active.append(n);used+=c
if active: modules.append(active)
owner={tag:i for i,group in enumerate(modules) for tag in group}
for i,group in enumerate(modules):
    deps=sorted({owner[ch] for n in group for ch in records[n][3] if owner[ch]!=i})
    text='import Cut\n'+''.join(f'import Part{k}\n' for k in deps)
    text+=f'namespace {namespace}\n'
    for n in group:
        k,t,ws,cut,c=records[n]
        text+=f'def state{n} : Nat × List Sig := {literal(t,ws)}\n'
        text+=f'set_option maxHeartbeats 0 in\nset_option maxRecDepth 60000 in\ntheorem no{n} : search {k} state{n}.1 state{n}.2 = false := by\n'
        if not cut:
            text+='  decide +kernel\n'
        else:
            denied='['+', '.join(f'state{ch}' for ch in cut)+']'
            text+=f'  apply prune {k-1} state{n}.1 state{n}.2 {denied}\n'
            text+='  · intro p hm\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm\n'
            text+='    rcases hm with '+' | '.join('rfl' for _ in cut)+'\n'
            text+=''.join(f'    · exact no{ch}\n' for ch in cut)
            text+='  · decide +kernel\n'
    (out/f'Part{i}.lean').write_text(text+f'end {namespace}\n')
for j in range(31):
    ns=root_ids[3*j:3*j+3]
    imports=sorted({owner[n] for n in ns})
    text='import Groups\n'+''.join(f'import Part{i}\n' for i in imports)+f'namespace {namespace}\n'
    text+=f'theorem checked{j} : group{j}.all reject = true := by\n'
    text+='  apply List.all_eq_true.mpr\n  intro p hm\n'
    text+=f'  simp only [group{j}, List.mem_cons, List.not_mem_nil, or_false] at hm\n'
    text+='  rcases hm with '+' | '.join('rfl' for _ in ns)+'\n'
    text+=''.join(f'  · simpa only [reject, Bool.not_eq_true\', state{n}] using no{n}\n' for n in ns)
    (out/f'Batch{j}.lean').write_text(text+f'end {namespace}\n')
(out/'order').write_text('\n'.join(f'Part{i}' for i in range(len(modules)))+'\n'+'\n'.join(f'Batch{i}' for i in range(31))+'\n')
print(len(records),'certificates;',len(modules),'parts;',sum(r[-1] for r in records),'residual nodes',flush=True)

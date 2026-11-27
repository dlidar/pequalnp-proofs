"""Classify repairs for the output of every binary straight-line prefix of length <=4."""
import json
from collections import Counter
from pathlib import Path
p=Path(__file__).resolve().parent
D=json.loads((p/'bounds.json').read_text());P,N=D['positive'],D['negative'];rows=P+N
T=(p/'table.bin').read_bytes();lo=(1<<len(P))-1;hi=(1<<len(N))-1
raw=[sum((x>>i&1)<<j for j,x in enumerate(rows)) for i in range(8)]
def cost(t):
 a=(~t)&lo;b=t>>len(P)
 return T[(a<<len(N))+b] if a and b else 0
def visit():
 # Only gates feeding the output matter. Merge indistinguishable boundary
 # signals and discard duplicated signals without altering any later trace.
 levels=[set(raw)];prior=set(raw)
 # For up to four gates, disconnected dead wires can be padded away.
 states={tuple()}
 programs=[]; examples={}
 for depth in range(1,5):
  nxt=set();outs=set()
  for state in states:
   wires=(*raw,*state);possible=set()
   for i,a in enumerate(wires):
    for b in wires[:i]:possible.update((a&b,a|b))
   possible.difference_update(wires)
   outs.update(possible)
   if depth<4:nxt.update(tuple(sorted((*state,t))) for t in possible)
  fresh=outs-prior;prior|=outs;levels.append(fresh)
  states=nxt
  print(depth,len(fresh),len(nxt),flush=True)
 hist=[dict(sorted(Counter(cost(t) for t in level).items())) for level in levels]
 for depth,level in enumerate(levels):
  t=min(level,key=lambda t:(-cost(t),t));examples[str(depth)]=[t,cost(t)]
 result=dict(leaf_cost_histograms=hist,hardest_examples=examples,distinct=len(prior),full_repair_histogram=dict(sorted(Counter(T[(a<<len(N))+b] if a and b else 0 for a in range(lo+1) for b in range(hi+1)).items())))
 (p/'catalog.json').write_text(json.dumps(result,indent=2)+'\n');print(hist)
if __name__=='__main__':visit()

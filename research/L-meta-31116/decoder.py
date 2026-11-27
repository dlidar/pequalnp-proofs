"""Exact support constraints for decoders following each shortest extremal prefix."""
from itertools import combinations
from pathlib import Path
import json
from upper import target
p=Path(__file__).resolve().parent
c=json.loads((p/'census.json').read_text());boundary=c['positive']+c['negative']
raw=[sum((x>>i&1)<<j for j,x in enumerate(boundary)) for i in range(8)]
def programs(row):
 available=raw.copy();extra=[]
 def rec(left):
  if not left:
   yield tuple(extra);return
  for s in left if len(left)>1 else [h]:
   if s==h and len(left)>1:continue
   for a,b in combinations(range(len(available)),2):
    for op,v in [('and',available[a]&available[b]),('or',available[a]|available[b])]:
     if s!=v:continue
     available.append(s);extra.append((op,a,b))
     yield from rec(left-{s})
     available.pop();extra.pop()
 h=row[-1];yield from rec(set(row))
def columns(g,x):
 w=[x>>j&1 for j in range(8)]
 for op,a,b in g:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
 w.append(1-w[-1]);return sum(v<<i for i,v in enumerate(w))
def classify(g):
 W=[columns(g,x) for x in range(256)]
 P=[x for x in range(256) if target(x) and not any(target(y) and W[y]!=W[x] and W[y]&W[x]==W[y] for y in range(256))]
 N=[x for x in range(256) if not target(x) and not any(not target(y) and W[y]!=W[x] and W[y]&W[x]==W[x] for y in range(256))]
 seps={W[x]&~W[y] for x in P for y in N};minimal=sorted(v for v in seps if not any(t!=v and t&v==t for t in seps))
 masks=[s for s in range(1<<13) if (s.bit_count()<=10) and all(s&t for t in minimal)]
 return dict(positive=P,negative=N,cuts=minimal,support=min(s.bit_count() for s in masks),supports=[s for s in masks if s.bit_count()==min(k.bit_count() for k in masks)] if len(masks)<150 else [])
out=[]
for line in (p/'worst-programs.txt').read_text().splitlines():
 row=list(map(int,line.split()));seen=set()
 for g in programs(row):
  W=[columns(g,x) for x in range(256)]
  sig=tuple(sorted(sum((v>>j&1)<<i for i,v in enumerate(W)) for j in range(8,13)))
  if sig in seen:continue
  seen.add(sig)
  r=classify(g);r['gates']=g;r['prefix_signature']=row;out.append(r)
  print(g,'support',r['support'],'counts',len(r['positive']),len(r['negative']),'cuts',r['cuts'],flush=True)
(p/'decoders.json').write_text(json.dumps(out,indent=1))

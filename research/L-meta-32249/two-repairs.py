from pathlib import Path
import itertools,json
import upper
p=Path(__file__).resolve().parent;O=set(upper.edges);raw=[sum(((x>>j)&1)<<x for x in range(256)) for j in range(8)];ALL=(1<<256)-1
truth=0
for i,j in O:truth|=raw[i]&raw[j]
def step(w,g):
 op,i,j=g
 return (w[i]&w[j]) if op=='and' else ((w[i]|w[j]) if op=='or' else ALL^w[i])
def walk(gs):
 opts=[[(op,a,b) for a,b in itertools.combinations(range(8+j),2) for op in ('and','or')]+[('not',a,0) for a in range(8+j)] for j in range(14)]
 base=raw.copy()
 for g in gs:base.append(step(base,g))
 for i in range(14):
  for first in opts[i]:
   q=base[:8+i];q.append(step(q,first))
   for g in gs[i+1:]:q.append(step(q,g))
   if q[-1]==truth:
    final=gs.copy();final[i]=first
    (p/'repair-witness.txt').write_text(json.dumps(final));return True
 for i in range(13):
  for first in opts[i]:
   w=base[:8+i];w.append(step(w,first))
   if w[-1]==base[8+i]:continue
   for j in range(i+1,14):
    # Equal intermediate truth tables are interchangeable throughout this suffix.
    seen=set()
    for second in opts[j]:
     if first[0]==second[0]=='not':continue
     v=step(w,second)
     if v in seen:continue
     seen.add(v);q=w+[v]
     for g in gs[j+1:]:q.append(step(q,g))
     if q[-1]==truth:
      final=gs.copy();final[i]=first;final[j]=second
      (p/'repair-witness.txt').write_text(json.dumps(final));return True
    w.append(step(w,gs[j]))
 return False
for delta,errors in json.loads((p/'nearest.json').read_text()):
 if len(errors)!=1:continue
 upper.edges=sorted(O^{tuple(e) for e in delta});upper.aset=set(upper.edges);g=upper.witnesses()['gates']
 if len(g)==14:
  hit=walk(g);print(delta,hit,flush=True)
  if hit:break

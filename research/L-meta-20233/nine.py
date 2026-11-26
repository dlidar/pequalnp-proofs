"""Synthesize a shared-OR/product decoder on nine encoded wires and check the assembled circuit."""
from pathlib import Path
from itertools import combinations
import json, subprocess,shutil
d=Path(__file__).parent;m=14466700110149527140
raw=[sum(1<<i for i in range(64) if j in (i//8,8+i%8)) for j in range(16)]
T=[x|y for x in (0,1,2) for y in (0,4,8)]
enc=json.loads((d/'four-encoders.json').read_text())
solver=shutil.which('cadical') or next(Path('work/lean-runtime/toolchains').glob('*/bin/cadical')).resolve()
def go(s,merged,cap,ix):
 gates=[];w=raw[:]
 def gate(op,a,b):
  gates.append((op,a,b));w.append(w[a]&w[b] if op=='and' else w[a]|w[b]);return len(w)-1
 sub=[i for i in range(16) if s>>i&1];cache={sum(1<<i for i,t in enumerate(T) if t>>j&1):l for j,l in enumerate(sub)}
 _,a,b,defs=next(e[1][0] for e in enc if e[0]==s)
 for op,x,y,z in defs:cache[z]=gate(op,cache[x],cache[y])
 ids=[cache[a],cache[b]];used=s
 for i,j in merged:ids.append(gate('or',i,8+j));used|=1<<i|1<<(8+j)
 ids += [i for i in range(16) if not used>>i&1]
 assert len(ids)==9
 nprep=len(gates)
 def subs(s):
  x=s
  while x:yield x;x=(x-1)&s
 masks=[0]*(1<<len(ids))
 for i in range(1,len(masks)):masks[i]=masks[i&(i-1)]|w[ids[(i&-i).bit_length()-1]]
 opts=[]
 for a in range(1,len(masks)):
  if not masks[a]&~m and a.bit_count()==1:opts.append((a,0,masks[a]))
  for b in range(1,a):
   z=masks[a]&masks[b]
   if not z or z&~m:continue
   if any(masks[a^(1<<j)]&masks[b]==z for j in range(9) if a>>j&1):continue
   if any(masks[b^(1<<j)]&masks[a]==z for j in range(9) if b>>j&1):continue
   if z in (masks[a],masks[b]):continue
   opts.append((a,b,z))
 groups=sorted({t for a,b,_ in opts for q in (a,b) for t in subs(q) if t.bit_count()>1})
 G={v:i+len(opts)+1 for i,v in enumerate(groups)};n=len(opts)+len(G)
 cs=[[h for h,(_,_,t) in enumerate(opts,1) if t>>i&1] for i in range(64) if m>>i&1]
 def fresh():
  nonlocal n
  n+=1;return n
 for i,(a,b,t) in enumerate(opts,1):
  for v in (a,b):
   if v in G:cs.append([-i,G[v]])
 pairs={}
 for v,h in G.items():
  pairs[v]=[(a,b) for a in subs(v) for b in subs(v) if a<b<v and a|b==v]
  if v.bit_count()==2:continue
  clause=[-h]
  for a,b in pairs[v]:
   need=[G[z] for z in (a,b) if z in G]
   if len(need)==1:clause+=need
   else:
    y=fresh();cs.extend([[-y,u] for u in need]);clause.append(y)
  cs.append(clause)
 def tally(xs,k):
  if len(xs)==1:return xs
  mid=len(xs)//2;a=tally(xs[:mid],k);b=tally(xs[mid:],k);r=[fresh() for _ in range(min(len(xs),k))]
  for i in range(len(a)+1):
   for j in range(len(b)+1):
    if 0<i+j<=len(r):cs.append(([-a[i-1]] if i else [])+([-b[j-1]] if j else [])+[r[i+j-1]])
  return r
 bound=cap-nprep+1
 tokens=[i for i,(a,b,t) in enumerate(opts,1) for _ in range(2 if b else 1)]+list(G.values())
 cs.append([-tally(tokens,bound+1)[bound]])
 name=f'nine-{ix}-{cap}';file=d/(name+'.cnf');log=d/(name+'.log')
 with file.open('w') as f:
  print('p cnf',n,len(cs),file=f)
  for c in cs:print(*c,0,file=f)
 with log.open('w') as out:r=subprocess.run([solver,'-t','15',file],stdout=out)
 print(ix,'prep',nprep,'budget',cap,'terms',len(opts),'result',r.returncode,flush=True)
 if r.returncode!=10:return
 model={int(x) for l in log.read_text().splitlines() if l.startswith('v ') for x in l[2:].split()}
 ws={1<<i:u for i,u in enumerate(ids)}
 for v in sorted(groups,key=int.bit_count):
  if G[v] in model:
   a,b=next((a,b) for a,b in pairs[v] if a in ws and b in ws);ws[v]=gate('or',ws[a],ws[b])
 outputs=[gate('and',ws[a],ws[b]) if b else ws[a] for i,(a,b,t) in enumerate(opts,1) if i in model]
 root=outputs[0]
 for x in outputs[1:]:root=gate('or',root,x)
 assert w[root]==m and len(gates)<=cap
 print('verified circuit',len(gates),flush=True);(d/f'nine-{ix}-circuit.json').write_text(json.dumps(gates))
 if len(gates)<=23:(d/'witness.json').write_text(json.dumps(gates))
for ix,(s,p) in enumerate(json.loads((d/'combined.json').read_text())['choices']):
 for cap in (23,24,25,26,27):
  if (d/'witness.json').exists() or (d/'stop').exists() or (d/'lost').exists():break
  go(s,p,cap,ix)
  if (d/f'nine-{ix}-circuit.json').exists():break

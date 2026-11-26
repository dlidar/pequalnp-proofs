"""Exact synthesis for a separate-OR / product / final-OR decoder after the six fixed identifications."""
from pathlib import Path
import json, shutil, subprocess
from check_rup import verify
d=Path(__file__).parent
m=14466700110149527140
w=json.loads((d/'matching-profile.json').read_text())['maximum_matchings'][0]
col={b:a for a,b in w}
v=sorted(set(range(8))|{col.get(i,8+i) for i in range(8)})
codes=[1<<v.index(i) | 1<<v.index(col.get(j,8+j)) for i in range(8) for j in range(8)]
def subs(s):
 a=s
 while a:yield a;a=(a-1)&s
def truth(s):return sum(1<<i for i,c in enumerate(codes) if s&c)
gm={s:truth(s) for s in range(1,1<<len(v))}
for j in range(len(v)):assert gm[1<<j]&~m
terms=[]
for a,t in gm.items():
 bmax=sum(1<<j for j in range(len(v)) if not (a>>j&1 or t&gm[1<<j]&~m))
 for b in subs(bmax):
  if a<b and t&gm[b]:terms.append((a,b,t&gm[b]))
groups=sorted({u for a,b,_ in terms for s in (a,b) for u in subs(s) if u.bit_count()>=2})
G={s:len(terms)+1+i for i,s in enumerate(groups)}
n=len(terms)+len(groups)
def fresh():
 global n
 n+=1;return n
cs=[[i for i,(_,_,t) in enumerate(terms,1) if t>>k&1] for k in range(64) if m>>k&1]
for i,(a,b,_) in enumerate(terms,1):
 for x in (a,b):
  if x in G:cs.append([-i,G[x]])
for s in groups:
 if s.bit_count()==2:continue
 # Any OR whose inputs are strict submasks of s with union s can form the group.
 proper=[x for x in subs(s) if x!=s]; opts=[]
 for i,a in enumerate(proper):
  for b in proper[i+1:]:
   if a|b!=s:continue
   need=[G[x] for x in (a,b) if x in G]
   if len(need)==1:opts+=need
   else:
    h=fresh();opts.append(h);cs.extend([[-h,z] for z in need])
 cs.append([-G[s],*set(opts)])
def tally(xs,bound):
 if len(xs)==1:return xs
 mid=len(xs)//2;left=tally(xs[:mid],bound);right=tally(xs[mid:],bound)
 out=[fresh() for _ in range(min(len(xs),bound))]
 for i in range(len(left)+1):
  for j in range(len(right)+1):
   if 0<i+j<=len(out):cs.append(([-left[i-1]] if i else [])+([-right[j-1]] if j else [])+[out[i+j-1]])
 return out
# Six preprocessing OR gates are fixed, leaving 17 decoder gates and at most 18 charged units.
tokens=list(range(1,len(terms)+1))*2+list(G.values())
cs.append([-tally(tokens,19)[18]])
file=d/'quotient17.cnf'
with file.open('w') as f:
 print('p cnf',n,len(cs),file=f)
 for c in cs:print(*c,0,file=f)
solver=shutil.which('cadical') or next(Path('work/lean-runtime/toolchains').glob('*/bin/cadical')).resolve()
proof=d/'quotient17.lrat'
print('terms',len(terms),'groups',len(groups),'clauses',len(cs),flush=True)
with (d/'quotient17.log').open('w') as out:r=subprocess.run([solver,'--plain','--lrat','--no-binary','-t','150',file,proof],stdout=out)
print('exit',r.returncode,flush=True)
if r.returncode==20:
 count=verify(file,proof)
 (d/'quotient-certified').write_text(str(count))
 print('verified additions',count,flush=True)

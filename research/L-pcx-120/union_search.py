"""Search a pool of relabeled PHP(4,3) resolution proofs for a shorter proof.

A selected line has a justification using selected earlier lines. The bound
counts the 22 mandatory initial clauses as well as all selected conclusions.
"""
from pathlib import Path
from itertools import permutations,combinations
import subprocess,random,sys,json,os,shutil
from dictionary import load
root=Path(__file__).resolve().parent
ref=Path(os.environ.get('PHP_REFERENCE', str(root.parents[1]/'lean/PEqualNP/Outside/L_pcx_123.lean')))
base=load(ref.read_text());actions=[(r,c) for r in permutations(range(4)) for c in permutations(range(3))]
def relab(q,act):
 r,c=act
 def move(t):
  i,h=divmod(abs(t)-1,3);return (1 if t>0 else -1)*(3*r[i]+c[h]+1)
 return frozenset(map(move,q))
def encode(copies,limit):
 rng=random.Random(120);others=actions[1:];rng.shuffle(others);rows=[actions[0],*others[:copies-1]]
 stage={}
 for a in rows:
  for k,c in enumerate(base):
   t=relab(c,a);stage[t]=min(k,stage.get(t,58))
 ax=set(base[:22]);lines=base[:22]+sorted(set(stage)-ax,key=lambda c:(stage[c],tuple(sorted(c))))
 assert lines[-1]==frozenset();index={c:i for i,c in enumerate(lines)}
 why=[[] for c in lines]
 for i,c in enumerate(lines):
  for j in range(i):
   d=lines[j]
   if d<c:why[i].append((j,))
   for t in c:
    if -t not in d:continue
    h=index.get((c-{t})|(d-{-t}))
    if h is not None and h>i:why[h].append((j,i))
 nv=len(lines);cnf=[]
 def fresh():
  nonlocal nv
  nv+=1;return nv
 for i in range(22):cnf.append([i+1])
 cnf.append([len(lines)])
 for i in range(22,len(lines)):
  votes=[]
  for parents in why[i]:
   if len(parents)==1:votes.append(parents[0]+1);continue
   w=fresh();votes.append(w)
   for p in parents:cnf.append([-w,p+1])
  cnf.append([-(i+1),*votes])
 # Forward sequential counter for the selected non-axioms.
 k=limit-22;last=[]
 for i in range(22,len(lines)):
  x=i+1;now=[fresh() for _ in range(min(k,i-21))]
  cnf.append([-x,now[0]])
  for j,v in enumerate(last):
   cnf.append([-v,now[j]])
   cnf.append([-x,-v,*([now[j+1]] if j+1<len(now) else [])])
  last=now
 p=root/f'pool{copies}-{limit}.cnf'
 with p.open('w') as f:
  f.write(f'p cnf {nv} {len(cnf)}\n')
  f.writelines(' '.join(map(str,c))+' 0\n' for c in cnf)
 return p,lines,why
def run(copies,limit,secs):
 p,lines,why=encode(copies,limit);sol=os.environ.get('CADICAL') or shutil.which('cadical')
 if not sol:raise RuntimeError('Specify CADICAL as the path to the pinned toolchain solver')
 log=p.with_suffix('.log')
 with log.open('w') as f:r=subprocess.run([sol,'-t',str(secs),p],stdout=f)
 print(copies,limit,len(lines),r.returncode,flush=True)
 if r.returncode==10:
  S={int(x)-1 for l in log.read_text().splitlines() if l.startswith('v ') for x in l[2:].split() if 1<=int(x)<=len(lines)}
  assert len(S)<=limit and len(lines)-1 in S and set(range(22))<=S
  proof={i:next(p for p in why[i] if set(p)<=S) for i in sorted(S) if i>=22}
  def dump(c):return sorted(c)
  p.with_suffix('.json').write_text(json.dumps({'lines':list(map(dump,lines)),'selected':sorted(S),'steps':proof}))
 return r.returncode
if __name__=='__main__':
 assert run(1,58,30)==10
 run(12,51,150)

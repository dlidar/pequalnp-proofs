"""Search a bounded edit neighborhood of the 23-gate circuit missing (1,2)."""
from search import d,encode,solver,rows,m
import fcntl,json,subprocess,itertools,time
from pathlib import Path
def test(seed,budget,seconds):
 n,cs,sel=encode(len(seed))
 flags=[]
 for (op,opts),(kind,a,b) in zip(sel,seed,strict=True):
  a,b=sorted([a,b]);n+=1;flags.append(n)
  cs.extend([[n,z] for z in (op if kind=='and' else -op,opts[0][a],opts[1][b])])
 def tally(xs):
  nonlocal n
  if len(xs)==1:return xs
  k=len(xs)//2;left=tally(xs[:k]);right=tally(xs[k:])
  out=list(range(n+1,n+1+min(len(xs),budget+1)));n+=len(out)
  for i in range(1+len(left)):
   for j in range(1+len(right)):
    if 0<i+j<=len(out):cs.append(([-left[i-1]] if i else [])+([-right[j-1]] if j else [])+[out[i+j-1]])
  return out
 cs.append([-tally(flags)[budget]])
 f=d/f'edit{budget}.cnf';log=f.with_suffix('.log')
 with f.open('w') as out:
  print('p cnf',n,len(cs),file=out)
  for c in cs:print(*c,0,file=out)
 with log.open('w') as out:r=subprocess.run([solver,'-t',str(seconds),f],stdout=out)
 print('edit budget',budget,'result',r.returncode,flush=True)
 if r.returncode!=10:return
 model={int(x) for line in log.read_text().splitlines() if line.startswith('v ') for x in line[2:].split()}
 gs=[['and' if op in model else 'or',*[next(i for i,v in enumerate(opts) if v in model) for opts in S]] for op,S in sel]
 for i,row in enumerate(rows):
  x=[row>>j&1 for j in range(16)]
  for op,a,b in gs:x.append(x[a]&x[b] if op=='and' else x[a]|x[b])
  assert x[-1]==m>>i&1
 (d/'witness.json').write_text(json.dumps(gs))
if __name__=='__main__':
 lock=(d/'repair.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 seed=json.loads((d/'edit-best.json').read_text())
 for k,s in [(3,100),(5,180),(8,240)]:
  if (d/'stop').exists() or (d/'lost').exists() or (d/'witness.json').exists():break
  test(seed,k,s)

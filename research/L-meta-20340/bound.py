from boxes import *
import subprocess
import shutil
solver=shutil.which("cadical") or next(Path("work/lean-runtime/toolchains").glob("*/bin/cadical")).resolve()
# Every cover constraint has exactly one positive-hit requirement or is a Horn dependency.
cs=[[var+1 if sign>0 else -(var+1) for var,sign in terms.items()] for terms in C]
# AND and final OR aggregation charge two tokens per chosen rectangle; final output rebates one.
hi=N
def fresh():
 global hi
 hi+=1;return hi
def tally(xs,limit):
 if len(xs)==1:return xs
 mid=len(xs)//2;a=tally(xs[:mid],limit);b=tally(xs[mid:],limit)
 out=[fresh() for _ in range(min(len(a)+len(b),limit))]
 for i in range(len(a)+1):
  for j in range(len(b)+1):
   if 0<i+j<=len(out):cs.append(([-a[i-1]] if i else [])+([-b[j-1]] if j else [])+[out[i+j-1]])
 return out
out=tally([h+1 for h in range(N) for _ in range(2 if h<n else 1)],29)
cs.append([-out[28]])
file=d/'restricted.cnf'
with file.open('w') as f:
 print('p cnf',hi,len(cs),file=f)
 for c in cs:print(*c,0,file=f)
with (d/'restricted.log').open('w') as f:r=subprocess.run([solver,'--plain','--lrat','--no-binary','-t','180',file,d/'restricted.lrat'],stdout=f)
if r.returncode==20:
 from check_rup import verify
 count=verify(file,d/'restricted.lrat')
 (d/'certified').write_text(str(count))

"""Build both optimal separated circuits and check every input."""
from cutwidth import *
import subprocess
D={}
for l in (p/'encoder-prices.txt').read_text().splitlines():
 t,c,*f=map(int,l.split());D[t,tuple(f)]=c
C=json.loads((p/'decoder-circuit-prices.json').read_text());tab={}
for l in (p/'five-costs').read_text().splitlines():
 z,k,op,a,b=l.split();tab[int(z)]=int(k),op,int(a),int(b)
choices=[]
for t,R in [(83,C[:108]),(86,C[108:])]:
 costs=[(min(D[t,tuple(a)],8)+min(D[t^255,tuple(b)],8)+v,D[t,tuple(a)],D[t^255,tuple(b)],v,a,b) for a,b,v in R]
 lo,k,l,v,a,b=min(costs);assert k<=7 and l<=7
 choices.append((t,lo,a,b,v))
 lines= [str(t)+' '+str(len(a))+' '+' '.join(map(str,a)),str(t^255)+' '+str(len(b))+' '+' '.join(map(str,b))]
 run=subprocess.run([p/'encoder-witness','7'],input='\n'.join(lines)+'\n',text=True,capture_output=True,check=True)
 states={}
 for line in run.stderr.splitlines():
  if line.startswith('witness '):
   _,i,c,*ds=line.split();states[int(i)]=list(map(int,ds));assert int(c)==len(ds)
 gs=[];out=[];X=masks(t);Y=masks(t^255)
 for side,block,funcs in [(0,t,a),(1,t^255,b)]:
  verts=[j for j in range(8) if block>>j&1]
  mp={sum((x>>i&1)<<x for x in range(16)):j for i,j in enumerate(verts)}
  remaining=set(states[side])
  while remaining:
   for i,j in itertools.combinations(list(mp),2):
    for op,z in [('and',i&j),('or',i|j)]:
     if z in remaining:gs.append([op,mp[i],mp[j]]);mp[z]=7+len(gs);remaining.remove(z);break
    else:continue
    break
   else:raise AssertionError('unreachable joint function')
  out+= [mp[f] for f in funcs]
 pos=neg=0
 for i,x in enumerate(X):
  for j,y in enumerate(Y):
   z=sum(((f>>i)&1)<<q for q,f in enumerate(a))+sum(((f>>j)&1)<<(q+len(a)) for q,f in enumerate(b))
   if fun(x|y):pos|=1<<z
   else:neg|=1<<z
 z=next(f for f,(k,_,_,_) in tab.items() if k==v+1 and f&pos==pos and not f&neg)
 def formula(f):
  _,op,x,y=tab[f]
  if op=='v':return out[x]
  assert op in ('&','|')
  i,j=formula(x),formula(y);gs.append(['and' if op=='&' else 'or',i,j]);return len(gs)+7
 output=formula(z)
 assert len(gs)==lo and output==len(gs)+7
 for x in range(256):
  bits=[x>>j&1 for j in range(8)]
  for op,i,j in gs:bits.append((bits[i]&bits[j]) if op=='and' else (bits[i]|bits[j]))
  assert bits[output]==fun(x)
 (p/f'balanced-{t}.json').write_text(json.dumps(dict(block=t,gate_count=lo,signals=out,gates=gs,output=output)))
 print(t,lo,'all 256 inputs verified')

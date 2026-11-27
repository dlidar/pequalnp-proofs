from cutwidth import *
from collections import Counter
D=json.loads((p/'balanced-encoders.json').read_text());tab={}
for line in (p/'five-costs').read_text().splitlines():
 t,c,op,a,b=line.split();tab[int(t)]=(int(c),op,int(a),int(b))
seq=sorted(tab,key=lambda t:(tab[t][0],t))
def case(t,enc,other):
 A,B=masks(t),masks(t^255);pos=neg=0
 for i,x in enumerate(A):
  s=sum(((f>>i)&1)<<j for j,f in enumerate(enc))
  for l,y in enumerate(B):
   code=s+sum(((f>>l)&1)<<(j+len(enc)) for j,f in enumerate(other))
   if fun(x|y):pos|=1<<code
   else:neg|=1<<code
 assert not pos&neg
 z=next(t for t in seq if t&pos==pos and not t&neg)
 return [pos,neg,z,tab[z][0]-1]
out={};used=set()
for t in (83,86):
 rec=[case(t,e,g) for e in D[str(t)] for g in D[str(t^255)]]
 print(t,Counter(z[3] for z in rec));out[t]=rec;used.update(z[2] for z in rec)
print('distinct attaining formulas',len(used))
(p/'decoder-cost.json').write_text(json.dumps(out))

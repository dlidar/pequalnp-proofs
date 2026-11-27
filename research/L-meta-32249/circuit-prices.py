from cutwidth import *
from collections import Counter
D=json.loads((p/'decoder-cost.json').read_text());cost={int(t):int(k) for t,k in (s.split() for s in (p/'decoder-tables').read_text().splitlines())}
E=json.loads((p/'balanced-encoders.json').read_text());out=[]
for ss,rows in D.items():
 t=int(ss);prices=[]
 for (a,b),(pos,neg,_,formula) in zip(itertools.product(E[ss],E[str(t^255)]),rows,strict=True):
  v=min([formula]+[k for z,k in cost.items() if z&pos==pos and not z&neg])
  prices.append(v);out.append([a,b,v])
 print(t,Counter(prices))
(p/'decoder-circuit-prices.json').write_text(json.dumps(out))
with (p/'encoder-queries.txt').open('w') as f:
 for t,R in E.items():
  for row in R:print(t,len(row),*row,file=f)

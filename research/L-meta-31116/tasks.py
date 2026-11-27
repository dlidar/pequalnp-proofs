from pathlib import Path
import json
from decoder import columns
from upper import target
p=Path(__file__).resolve().parent
cases=json.loads((p/'decoders.json').read_text());d=json.loads((p/'census.json').read_text())
def save(name,P,N,signals,n):
 (p/name).write_text(f'{len(P)} {len(N)} {n}\n'+' '.join(str(sum((signals(x)>>i&1)<<j for j,x in enumerate(P+N))) for i in range(n))+'\n')
save('full.task',d['positive'],d['negative'],lambda x:x,8)
for i,r in enumerate(cases):save(f'prefix{i}.task',r['positive'],r['negative'],lambda x:columns(r['gates'],x),13)

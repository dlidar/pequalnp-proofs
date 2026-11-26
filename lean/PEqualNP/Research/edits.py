from pathlib import Path
import subprocess,json,re,collections
w=Path(__file__).parent
pairs=[(int(p),int(l)-21) for p,l in re.findall(r'x (\d+) && x (\d+)',(w/'PuncturedCircuits.lean').read_text().split('namespace Reference')[1].split('def target')[1].split('theorem correct')[0])]
rows=[sum(1<<l for p,l in pairs if p==q) for q in range(21)]
def count(rs):
 s=subprocess.check_output([w/'edits'],input=' '.join(map(str,rs)),text=True)
 return {(i,j):(e,v) for i,j,e,v in (map(int,line.split()) for line in s.splitlines())}
tab=count(rows)
dual=count([sum(1<<p for p,l in pairs if l==j) for j in range(21)])
assert all(v==dual[j,i] for (i,j),v in tab.items())
for e in range(2):
 print(e,sorted(collections.Counter(v for k,v in tab.values() if k==e).items()))
 print('nearest',min((v,p,j) for (p,j),(k,v) in tab.items() if k==e))
(w/'edit-counts.json').write_text(json.dumps([(*a,*b) for a,b in tab.items()]))

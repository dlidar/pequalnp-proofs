"""Exact deletion checks in the clause dictionary of upstream L_pcx_123."""
from itertools import combinations
from pathlib import Path
import re,json
def load(source):
 out=[]
 for k,body in re.findall(r'^def l(\d+) : LinClause VV := (.+)$',source,re.M):
  assert int(k)==len(out)
  lits=re.findall(r'\(\{\((\d), (\d)\)\} : Finset VV\), (true|false)',body)
  assert len(lits)==body.count('Finset VV') and (lits or '∅' in body)
  out.append(frozenset((3*int(i)+int(j)+1)*(1 if sign=='true' else -1) for i,j,sign in lits))
 assert len(out)==len(set(out))==58
 return out
def rules(lines):
 idx={c:i for i,c in enumerate(lines)}
 why=[[] for c in lines]
 for i,c in enumerate(lines):
  for j,d in enumerate(lines):
   # These non-tautological ordinary clauses are embedded as singleton
   # linear equations. Semantic weakening is exactly literal inclusion.
   assert not any(-x in c for x in c)
   if i!=j and c<d:why[j].append((i,))
   if j<=i:continue
   for x in c:
    if -x not in d:continue
    res=(c-{x})|(d-{-x})
    if res in idx:why[idx[res]].append((i,j))
 return why
def derive(why,ban):
 done=set(range(22))-{ban}
 while True:
  more={i for i,options in enumerate(why) if i!=ban and any(all(p in done for p in opt) for opt in options)}
  if more<=done:return done
  done|=more
def main(source):
 lines=load(source);why=rules(lines);assert 57 in derive(why,-1)
 needed=[j for j in range(58) if 57 not in derive(why,j)]
 print('indispensable',len(needed),'optional',[i for i in range(58) if i not in needed])
 data={'clauses':[sorted(c) for c in lines],'indispensable':needed}
 (Path(__file__).resolve().parent/'dictionary.json').write_text(json.dumps(data))
if __name__=='__main__':
 import sys
 main(Path(sys.argv[1]).read_text())

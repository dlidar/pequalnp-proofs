"""Verify an LRAT proof containing RUP additions and deletions; reject RAT hints."""
import sys
from pathlib import Path
def verify(cnf,proof):
 db={}
 with open(cnf) as f:
  for l in f:
   if l.startswith('p '):
    p,kind,num,numcl=l.split();assert kind=='cnf'
   elif l.strip() and not l.startswith('c'):
    v=list(map(int,l.split()));assert v.pop()==0 and all(x!=0 for x in v)
    db[len(db)+1]=tuple(set(v))
 assert len(db)==int(numcl)
 last=len(db);total=0;empty=False
 with open(proof) as f:
  for line in f:
   items=line.split()
   if items[1]=='d':
    assert items[-1]=='0'
    for k in map(int,items[2:-1]):db.pop(k,None)
    continue
   row=list(map(int,items));idx=row.pop(0);z=row.index(0);cl=tuple(set(row[:z]));hints=row[z+1:]
   assert idx>last and hints.pop()==0 and all(x>0 for x in hints);last=idx
   trues={-x for x in cl};conflict=False
   for hint in hints:
    old=db[hint];assert not any(t in trues for t in old)
    remaining=[t for t in old if -t not in trues]
    if not remaining:conflict=True;break
    assert len(remaining)==1
    trues.add(remaining[0])
   assert conflict
   db[idx]=cl;total+=1
   if not cl:empty=True
 assert empty
 return total
if __name__=='__main__':print('independently checked RUP additions',verify(*sys.argv[1:]))

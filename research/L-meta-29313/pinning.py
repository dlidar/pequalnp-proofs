"""Exact restriction lower bounds when raw inputs and one antitone signal feed a formula."""
from labels import *
import subprocess
def main():
 sol=subprocess.Popen([p/'smalldec'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
 cofs=[]
 for t in range(1,256):
  free=255^t;on=t
  while True:
   masks=[x for x in range(256) if x&t==on]
   P=[x for x in masks if graph(x) and all(not graph(x^(1<<j)) for j in range(8) if free&x&(1<<j))]
   N=[x for x in masks if not graph(x) and all(graph(x|(1<<j)) for j in range(8) if free&~x&(1<<j))]
   if not P or not N:v=0
   else:
    sol.stdin.write(' '.join(map(str,[len(P),len(N)]+P+N))+'\n');sol.stdin.flush();v=int(sol.stdout.readline())
   cofs.append((t,on,v,sum(1<<x for x in masks)))
   if not on:break
   on=(on-1)&t
 sol.stdin.close();sol.wait()
 assert len(cofs)==6560
 rows={}
 for k,op,i,j,h in cases:
  val,t,on=max((t.bit_count()+1+v,t,on) for t,on,v,m in cofs if h&m in (0,m))
  rows[hex(h)]=dict(lower_if_used=val,exact_lower=min(15,val),fixed=t,on=on)
 (p/'pinning.json').write_text(json.dumps(rows))
 from collections import Counter
 print('proper restrictions',len(cofs),'all raw supplements',[(i,rows[hex(h)]['lower_if_used']) for i,h in enumerate(raw)])
 print('all 64',Counter(x['lower_if_used'] for x in rows.values()))
if __name__=='__main__':main()

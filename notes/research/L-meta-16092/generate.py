"""Generate the Lean certificate partitions. Every generated branch is checked by the Lean kernel."""
from pathlib import Path
from functools import reduce,lru_cache
import json,itertools
w=Path(__file__).resolve().parent;pairs=json.loads((w/'pairs.json').read_text());M=(1<<64)-1;M2=(1<<128)-1
ROOT=tuple(sum(((a>>k)&1)<<j|((b>>k)&1)<<(64+j) for j,(a,b) in enumerate(pairs)) for k in range(6))
def sep(x):return ((x>>64)^x)&M
def children(extra,ws):
 for i,j in itertools.combinations(range(len(ws)),2):
  a,b=ws[i],ws[j];r=tuple(x for k,x in enumerate(ws) if k not in (i,j))
  mask=reduce(int.__or__,map(sep,r),0)
  for z in [a&b,a|b,a&~b,b&~a]:
   m=mask|sep(z)
   for keep in [(),(a,),(b,),(a,b)]:
    if extra>=len(keep) and reduce(int.__or__,map(sep,keep),m)==M:
     yield extra-len(keep),(z,)+keep+r
@lru_cache(maxsize=80000)
def weight(k,e,ws):
 if k==0:return 1
 return 1+sum(weight(k-1,ne,nw) for ne,nw in children(e,ws))

options='set_option maxRecDepth 64000\nset_option maxHeartbeats 10000000\n'
ns='PEqualNP.Research.Signed16092'
def lst(ws):return '['+', '.join(hex(x) for x in ws)+']'
def pair(e,ws):return '('+str(e)+', '+lst(ws)+')'
def close(name,k,e,ws,chs,refs,wsname=None):
 v=wsname or lst(ws)
 rhs='['+', '.join(pair(j,state) for j,state in chs)+']'
 proof='by simp'
 for ref in reversed(refs):proof='List.forall_mem_cons.mpr ⟨'+ref+', '+proof+'⟩'
 return f'''theorem {name} : optimized {k} {e} {v}=false := by
  apply reject_step {k-1} {e} {v} (by decide +kernel)
  have expand : children {e} {v} = {rhs} := by decide +kernel
  rw [expand]
  exact {proof}
'''
def gen(i,e,ws,limit):
 acc=[];known={}
 def visit(k,e,ws):
  key=(k,e,ws)
  if key in known:return known[key]
  count=weight(k,e,ws)
  if count>limit and k>0:
   ch=list(children(e,ws))
   refs=[visit(k-1,j,st) for j,st in ch]
   name=f'cut{i}_{len(acc)}'
   acc.append(close(name,k,e,ws,ch,refs))
  else:
   name=f'cut{i}_{len(acc)}'
   acc.append(f'theorem {name} : optimized {k} {e} {lst(ws)}=false := by decide +kernel\n')
  known[key]=name
  return name
 root=visit(7,e,ws)
 return '\n'.join(acc)+f'\ntheorem root{i} : optimized 7 {e} {lst(ws)}=false := {root}\n'
if __name__=='__main__':
 ch=list(children(3,ROOT)); names=[]
 for i,(e,ws) in enumerate(ch):
  (w/f'Root{i}.lean').write_text('import Frontier\nnamespace '+ns+'\n'+options+gen(i,e,ws,700)+'end '+ns+'\n');names.append('root'+str(i))
 root='\n'.join('import Root'+str(i) for i in range(len(ch)))+'\nnamespace '+ns+'\n'+options+close('root_checked',8,3,ROOT,ch,names,'rows')+'end '+ns+'\n'
 (w/'RootProof.lean').write_text(root)
 print(len(ch),'partitions',sum((w/f'Root{i}.lean').stat().st_size for i in range(len(ch))))

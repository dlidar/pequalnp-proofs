from pathlib import Path
from functools import lru_cache
from itertools import combinations
import re,sys
p=Path(__file__).resolve().parent/'split'
mask=(1<<84)-1
@lru_cache(None)
def children(ws,e):
 states={}
 for i,j in combinations(range(len(ws)),2):
  a,b=ws[i],ws[j];rest=tuple(v for h,v in enumerate(ws) if h!=i and h!=j)
  base=0
  for x in rest:base|=(x>>84)&~x
  for z in (a&b,a|b):
   for keep in ((),(a,),(b,),(a,b)):
    if len(keep)>e:continue
    cv=base|(z>>84)&~z
    for x in keep:cv|=(x>>84)&~x
    if cv&mask==mask:states[(e-len(keep),(z,)+keep+rest)]=1
 return tuple(states)
@lru_cache(maxsize=1000000)
def cost(ws,e,k):
 if ws==(mask<<84,):raise ValueError('found target')
 if not k:return 1
 return 1+len(ws)*(len(ws)-1)+sum(cost(l,t,k-1) for t,l in children(ws,e))
def fmt(ws):return '['+', '.join(map(hex,ws))+']'
ns='PEqualNP.Outside.Mask114591'
opts='set_option maxRecDepth 32000 in\nset_option maxHeartbeats 100000000 in\n'
written={};order=[]
def build(name,th,k,e,ws,limit):
 if (k,e,ws) in written:return written[k,e,ws]
 bound=cost(ws,e,k)
 head=f'theorem {th} : optimized {k} {e} {fmt(ws)} = false := by\n'
 ch=children(ws,e) if k else []
 if bound<=limit:
  text=f'import Core\nnamespace {ns}\n'+opts+head+'  decide +kernel\n'
 else:
  deps=[build(f'Piece{len(order)}x{name}',f'sub{len(order)}x{th}',k-1,t,ls,limit) for t,ls in ch]
  den=',\n    '.join(f'({t}, {fmt(ls)})' for t,ls in ch)
  text='import Prune\n'+''.join('import '+f+'\n' for f,_ in dict.fromkeys(deps))+f'namespace {ns}\n'+opts+head+f'  apply split_node {k-1} {e} _ [{den}]\n'
  if deps:
   text+='  · intro x hx\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n    rcases hx with '+' | '.join(['rfl']*len(deps))+'\n'+''.join(f'    · exact {lemma}\n' for _,lemma in deps)
  else:text+='  · simp\n'
  text+='  · decide +kernel\n  · decide +kernel\n'
 text+=f'end {ns}\n'
 (p/(name+'.lean')).write_text(text);order.append(name);written[k,e,ws]=(name,th);return name,th
roots=[]
for idx in range(36):
 f=p/f'Branch{idx}.lean'
 t=f.read_text().split('theorem br'+str(idx)+' : optimized ')[1]
 a=re.match(r'(\d+) (\d+) \[([^\]]+)\]',t);k,e=map(int,a.groups()[:2]);ws=tuple(int(x,16) for x in a[3].split(','))
 roots.append((idx,k,e,ws))
print('costs',[(idx,cost(ws,e,k)) for idx,k,e,ws in roots],flush=True)
if len(sys.argv)>1:
 for i,k,e,ws in roots:
  if i < 11:continue
  if cost(ws,e,k)>int(sys.argv[1]):
   build('Branch'+str(i),'br'+str(i),k,e,ws,int(sys.argv[1]))
  else:order.append('Branch'+str(i))
 (p/'order').write_text('\n'.join(order+['Lower'])+'\n')

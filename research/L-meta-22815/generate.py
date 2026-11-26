"""Specialize the Mask241139 Lean live-set proof to an assigned monotone promise graph."""
import sys,re,json,itertools
from functools import lru_cache
from pathlib import Path
root=Path(__file__).resolve().parent
a=json.loads(Path(sys.argv[1]).read_text())['gap'];d=Path(sys.argv[2]); d.mkdir(parents=True,exist_ok=True)
st=a['statement']; m=re.fullmatch(r'PEqualNP.Represents.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\) => \((\d+) : ℕ\).testBit \((\d+) \* u.val \+ v.val\)\) (\d+)',st)
assert m
n,c,M,c2,K=map(int,m.groups());assert c==c2
pos=[i for i in range(n*c) if (M>>i)&1];neg=[i for i in range(n*c) if not (M>>i)&1]
pairs=list(itertools.product(pos,neg));w=len(pairs);z=(1<<w)-1;goal=z<<w
samples=[b for a,b in pairs]+[a for a,b in pairs]
raw=[sum(1<<i for i,x in enumerate(samples) if j in (x//c,n+x%c)) for j in range(n+c)]
def sep(s):
 t=0
 for x in s:t|=(x>>w)&~x
 return t&z==z
@lru_cache(None)
def solve(s,k):
 if goal in s:return ()
 if not k or len(s)>k+1 or not sep(s):return
 for i,j in itertools.combinations(range(len(s)),2):
  a,b=s[i],s[j];rest=tuple(x for p,x in enumerate(s) if p not in (i,j))
  for op,v in [('and',a&b),('or',a|b)]:
   if v in s:continue
   for keep in [(),(a,),(b,),(a,b)]:
    if len(rest)+len(keep)>=k:continue
    r=solve(tuple(sorted(rest+keep+(v,))),k-1)
    if r is not None:return ((op,a,b,v),)+r
def witness(k):
 for ar in range(min(k+1,len(raw)),0,-1):
  for s in itertools.combinations(raw,ar):
   r=solve(tuple(sorted(s)),k)
   if r is not None:return r
r=witness(K);positive=r is not None
if not positive:r=witness(K+1)
assert r is not None
vals=raw[:];gs=[]
for op,a,b,v in r:gs.append((op,vals.index(a),vals.index(b)));vals.append(v)
out=vals.index(goal)
for j in range(n*c):
 vals=[i in (j//c,n+j%c) for i in range(n+c)]
 for op,a,b in gs:vals.append((vals[a] and vals[b]) if op=='and' else (vals[a] or vals[b]))
 assert vals[out]==bool((M>>j)&1)
print('Explicit witness',len(gs),'gates;',len(samples)//max(1,w),'signature halves;',n*c,'promised inputs checked',flush=True)
def shape(s):
 return s.replace('Mask241139','Mask'+str(M)).replace('241139 :',str(M)+' :').replace('Fin 4 → Fin 5','Fin %d → Fin %d'%(n,c)).replace('Fin 4 × Fin 5','Fin %d × Fin %d'%(n,c)).replace('(u : Fin 4) (v : Fin 5)','(u : Fin %d) (v : Fin %d)'%(n,c)).replace('(5 * u.val','(%d * u.val'%c)
up=shape((root/'template-Upper.lean').read_text())
up=re.sub(r'\{ gates := \[.*?output := \d+ \}',lambda m:'{ gates := ['+',\n      '.join('{ op := GateOp.%s, inputs := [%d, %d] }'%x for x in gs)+'], output := '+str(out)+' }',up,flags=re.S)
up=re.sub(r'rcases hg with .*? <;>','rcases hg with '+' | '.join(['rfl']*len(gs))+' <;>',up)
up=up.replace(')) 9 :=',')) '+str(K if positive else K+1)+' :=')
(d/'Upper.lean').write_text(up)
if positive:sys.exit()
s=shape((root/'template-Lower.lean').read_text())
s=re.sub(r'\b(91|182)\b',lambda m:str(w if m[0]=='91' else w*2),s)
s=re.sub(r'(def rawInputs : List W :=\s*)\[[^\]]+\]',lambda m:m[1]+'['+', '.join(map(hex,raw))+']',s)
for label,nums in [('posL',pos),('negL',neg)]:
 s=re.sub(r'(def '+label+r' [^\n]*? := )\[[^\]]*\]',lambda m:m[1]+str([divmod(i,c) for i in nums]),s)
s=s.replace('k.val % 7','k.val % '+str(len(neg))).replace(') / 7',') / '+str(len(neg)))
i=s.index('theorem front :');j=s.index('end PEqualNP',i)
s=s[:i]+re.sub(r'\b[89]\b',lambda m:str(K+int(m[0])-8),s[i:j])+s[j:]
s=re.sub(r'theorem exact_negation : ¬ .*? := by','theorem exact_negation : ¬ '+st+' := by',s)
(d/'Lower.lean').write_text(s)

"""Specialize the full AND/OR/NOT live-wire search to shared or split input promises."""
from pathlib import Path
import json,re,itertools,sys
D=Path(__file__).resolve().parent;g=json.loads(Path(sys.argv[1]).read_text())['gap'];d=Path(sys.argv[2]); d.mkdir(parents=True,exist_ok=True);st=g['statement']
K=int(re.search(r'C.size ≤ (\d+)',st)[1]);M=int(re.search(r'\((\d+) : ℕ\).testBit',st)[1])
shared='List.ofFn fun k' in st;n=int(re.search(r'(?:i j|u v) : Fin (\d+)',st)[1]);N=n if shared else 2*n
cells=list(itertools.combinations_with_replacement(range(n),2)) if shared else list(itertools.product(range(n),repeat=2))
def bits(r):return {r[0],r[1] if shared else n+r[1]}
def yes(r):return (M>>(n*r[0]+r[1]))&1
raw=[sum(1<<i for i,r in enumerate(cells) if j in bits(r)) for j in range(N)];goal=sum(yes(r)<<i for i,r in enumerate(cells))
src=(D/'not-find.py').read_text();src=src[:src.index('raw=[')]+src[src.index('@lru_cache'):src.index('for n in range(1,7):')]
ns=dict(raw=raw,goal=goal,ALL=(1<<len(cells))-1);exec(src,ns)
def solve(k):
 for l in range(min(k+1,N),0,-1):
  for ws in itertools.combinations(raw,l):
   h=ns['search'](tuple(sorted(ws)),k)
   if h is not None:return h
h=solve(K);positive=h is not None
if not positive:h=solve(K+1)
assert h is not None
ws=raw[:];gs=[]
for op,a,b,v in h:
 gs.append((op,[ws.index(a)] if op=='not' else [ws.index(a),ws.index(b)]));ws.append(v)
out=ws.index(goal)
for cell in cells:
 vals=[j in bits(cell) for j in range(N)]
 for op,ij in gs:
  vv=[vals[j] for j in ij];vals.append(all(vv) if op=='and' else any(vv) if op=='or' else not vv[0])
 assert vals[out]==yes(cell)
print('Witness',len(gs),'checked on',len(cells),'inputs',flush=True)
upper=st.replace('C.size ≤ '+str(K)+' ∧','C.size ≤ '+str(K if positive else K+1)+' ∧')
s='import Mathlib\nimport PEqualNP.Defs.Represents\nopen PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\nnamespace Mask'+str(M)+'Witness\n'
s+='def circuit : Circuit := ⟨['+', '.join('⟨.'+op+', '+str(ij)+'⟩' for op,ij in gs)+'], '+str(out)+'⟩\n'
s+='theorem upper : '+upper+' := by\n  refine ⟨circuit, ?_, by decide, by decide +kernel⟩\n  intro g hg\n  simp [circuit] at hg\n  rcases hg with '+' | '.join(['rfl']*len(gs))+' <;> simp\nend Mask'+str(M)+'Witness\n#print axioms Mask'+str(M)+'Witness.upper\n'
(d/'Upper.lean').write_text(s)
if positive:quit()
p=[r for r in cells if yes(r)];ne=[r for r in cells if not yes(r)];pairs=list(itertools.product(p,ne));W=len(pairs)
def sig(j,k):return sum(1<<i for i,z in enumerate(pairs) if j in bits(z[k]))
s=(D/'not-Lower.lean').read_text().replace('Mask5087','Mask'+str(M)).replace('0xfffffffffffffff',hex((1<<W)-1))
s=re.sub(r'\b(60|120)\b',lambda m:str(W if m[0]=='60' else 2*W),s)
s=re.sub(r'(def rawInputs : List Sig :=\s*)\[.*?\]',lambda m:m[1]+str([(sig(j,0),sig(j,1)) for j in range(N)]),s,flags=re.S)
i=s.index('def A (');j=s.index('theorem initial_rep',i)
fval=f'({M} : Nat).testBit ({n} * min u.val v.val + max u.val v.val)' if shared else f'({M} : Nat).testBit ({n}*u.val+v.val)'
inp=f'(List.ofFn fun k : Fin {n} => decide (k = u ∨ k = v))' if shared else '(PEqualNP.Represents.oneEach u v)'
s=s[:i]+f'''def A (u v : Fin {n}) : Bool := {fval}
def inp (u v : Fin {n}) := {inp}
def Correct (C : Circuit) := ∀ u v : Fin {n}, C.eval (inp u v) = A u v
def posL : List (Fin {n} × Fin {n}) := {p}
def negL : List (Fin {n} × Fin {n}) := {ne}
def sample (i : Fin {W*2}) := if i.val < {W} then negL.getD (i.val % {len(ne)}) (0,0) else posL.getD ((i.val-{W})/{len(ne)}) (0,0)
theorem input_rows : ∀ i : Fin {W*2}, rawInputs.map (bit i) = inp (sample i).1 (sample i).2 := by decide +kernel
theorem goal_rows : ∀ i : Fin {W*2}, bit i target = A (sample i).1 (sample i).2 := by decide +kernel
theorem rows_eval (C : Circuit) (he : Correct C) (k : Fin {W*2}) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k target := by
  rw [input_rows, goal_rows]
  exact he _ _
'''+s[j:]
s=s.replace('(he : PEqualNP.Represents.Represents A C)','(he : Correct C)')
i=s.index('theorem front :');j=s.index('end PEqualNP.Outside.',i)
s=s[:i]+re.sub(r'\b(5|6|7)\b',lambda m:str(K+int(m[0])-5),s[i:j])+s[j:]
s=re.sub(r'theorem exact_negation : ¬ .*? := by','theorem exact_negation : ¬ ('+st+') := by',s)
(d/'Lower.lean').write_text(s)

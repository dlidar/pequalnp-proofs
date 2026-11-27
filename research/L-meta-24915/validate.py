"""Read the dynamic programs' expressions, check every promised input and share repeated gates."""
from pathlib import Path
import itertools, json, re
root=Path(__file__).resolve().parent
cases=[('raw', (root/'formula.log').read_text().split()[-1])]
cases.extend((c,e) for c,d,e in (row.split() for row in (root/'cached.log').read_text().splitlines()))
best = None
proof = []
for cache, expression in cases:
    gates=[]
    seen={}
    def add(op,*args):
        key=(op, args if op=='!' else tuple(sorted(args)))
        if key not in seen:
            seen[key]=6+len(gates)
            gates.append(key)
        return seen[key]
    if cache!='raw':
        h=add('!',int(cache[1])) if cache.startswith('!') else add(cache[1],int(cache[0]),int(cache[2]))
    def parse(s):
        if s.isdigit(): return int(s)
        if s=='H': return h
        assert s[0]=='(' and s[-1]==')'
        s=s[1:-1]
        if s[0]=='!': return add('!',parse(s[1:]))
        depth=0
        for i,t in enumerate(s):
            if t=='(': depth+=1
            if t==')': depth-=1
            if depth==0 and t in '&|': return add(t,parse(s[:i]),parse(s[i+1:]))
        raise ValueError(s)
    out=parse(expression)
    for i,j in itertools.combinations_with_replacement(range(6),2):
        ws=[v in (i,j) for v in range(6)]
        for op,args in gates:
            a=ws[args[0]]
            ws.append(not a if op=='!' else a and ws[args[1]] if op=='&' else a or ws[args[1]])
        assert ws[out] == bool((4294973>>(6*i+j))&1)
    if cache=='raw': (root/'formula-witness.json').write_text(json.dumps([gates,out]))
    if best is None or len(gates)<best:
        best=len(gates)
        (root/'best-witness.json').write_text(json.dumps([gates,out]))
    proof.append((cache,len(gates),expression))
print('Evaluated',len(cases),'circuits on all 21 inputs. Smallest checked after sharing:',best)

"""Test twelve gates with two NOTs using the proved chain constraints and the nine-slot driver bound."""
from pathlib import Path
from itertools import combinations
import json,subprocess,shutil,sys
from check_rup import verify
from driver_sat import constraints
D=Path(__file__).resolve().parent
def make(n,first,second,rows,fix=None):
    req=constraints();length=len(rows);counter=0;clauses=[]
    def fresh(n):
        nonlocal counter
        counter+=n;return list(range(counter-n+1,counter+1))
    def one(ss):
        clauses.append(ss);clauses.extend([-a,-b] for a,b in combinations(ss,2))
    ws=[fresh(length) for _ in range(8+n)]
    for j in range(8):
        for i,x in enumerate(rows):
            y=ws[j][i];clauses.append([y if ((x>>j&1) if j<6 else j==7) else -y])
    record=[]
    for g in range(n):
        neg=g in (first,second);ports=[];v=[];op=fresh(1)[0]
        for j in range(1 if neg else 2):
            sel=fresh(8+g);one(sel);ports.append(sel);p=fresh(length);v.append(p)
            for k,s in enumerate(sel):
                for a,b in zip(ws[k],p):clauses.extend([[-s,-a,b],[-s,a,-b]])
        if not neg:
            for l,s in enumerate(ports[0]):
                for t in ports[1][:l]:clauses.append([-s,-t])
        for i,row in enumerate(rows):
            a=v[0][i];y=ws[8+g][i]
            if neg:
                clauses.extend([[a,y],[-a,-y]])
                if row in req:
                    need=req[row][0] if g==first else 1-req[row][1]
                    clauses.append([y if need else -y])
            else:
                b=v[1][i];clauses.extend([[-op,-a,-b,y],[-op,a,-y],[-op,b,-y],[op,a,b,-y],[op,-a,y],[op,-b,y]])
            if g==n-1:clauses.append([y if (row&7)>(row>>3) else -y])
        if fix:
            k,l,r=fix[g];assert (k=='not')==neg
            if not neg:
                l,r=sorted([l,r]);clauses.extend([[op if k=='and' else -op],[ports[1][r]]])
            clauses.append([ports[0][l]])
        record.append((neg,op,ports))
    return counter,clauses,record
def control():
    # With the complemented majority and parity of b available, every
    # complemented b literal has a monotone decoder on b and those signals.
    g=[]
    def ins(k,i,j=0):g.append((k,i,j));return len(g)+7
    def A(i,j):return ins('and',i,j)
    def O(i,j):return ins('or',i,j)
    lo=A(3,4);either=O(3,4);maj=O(lo,A(either,5));nm=ins('not',maj)
    par=O(A(nm,O(either,5)),A(lo,5));np=ins('not',par)
    # monotone DNF on the five-bit encodings of the eight possible b values
    vs=[3,4,5,nm,np];nb=[]
    for j in range(3):
        terms=[]
        for m in range(8):
            if m>>j&1:continue
            bits=[*(m>>k&1 for k in range(3)),m.bit_count()<2,m.bit_count()%2==0]
            vals=[i for i,b in zip(vs,bits) if b];p=vals[0]
            for v in vals[1:]:p=A(p,v)
            terms.append(p)
        a=terms[0]
        for t in terms[1:]:a=O(a,t)
        nb.append(a)
    lower=A(0,nb[0])
    for j in [1,2]:lower=O(A(j,nb[j]),A(O(j,nb[j]),lower))
    for row in range(64):
        w=[int(row>>k&1) for k in range(6)]+[0,1]
        for k,a,b in g:w.append(1-w[a] if k=='not' else w[a]&w[b] if k=='and' else w[a]|w[b])
        assert w[-1]==int((row&7)>(row>>3))
    return g,[i for i,(k,*_) in enumerate(g) if k=='not']
def solve(n,p,q,fix=None):
    solver=shutil.which('cadical') or next((D.parent/'lean-runtime/toolchains').glob('*/bin/cadical'))
    rows=list(range(64)) if fix else sorted(constraints())
    while True:
        nv,c,record=make(n,p,q,rows,fix)
        base='two-control' if fix else f'twelve-{p}-{q}'
        cnf=D/(base+'.cnf');proof=D/(base+'.lrat')
        with cnf.open('w') as f:
            print('p cnf',nv,len(c),file=f)
            for x in c:print(*x,0,file=f)
        r=subprocess.run([str(solver),'--lrat','--no-binary','-q','-t','90',str(cnf),str(proof)],capture_output=True,text=True)
        if r.returncode==20:return {'rows':rows,'checked_additions':verify(cnf,proof)}
        if r.returncode!=10:return {'unknown':True}
        if fix:return {'control':True}
        yes={int(tok) for line in r.stdout.splitlines() if line.startswith('v ') for tok in line.split()[1:]}
        gates=[]
        for neg,op,ports in record:
            ij=[next(i for i,s in enumerate(ss) if s in yes) for ss in ports]
            gates.append(('not' if neg else ('and' if op in yes else 'or'),ij))
        errors=[]
        for z in range(64):
            w=[int(z>>k&1) for k in range(6)]+[0,1]
            for op,ij in gates:w.append(1-w[ij[0]] if op=='not' else (w[ij[0]]&w[ij[1]]) if op=='and' else (w[ij[0]]|w[ij[1]]))
            if w[-1]!=int((z&7)>(z>>3)):errors.append(z)
        assert not set(rows).intersection(errors)
        if not errors:return {'witness':gates}
        rows=sorted(set(rows+errors))
if __name__=='__main__':
    g,ij=control();assert solve(len(g),*ij,fix=g)=={'control':True}
    print('full positive control',len(g),ij,flush=True)
    out={}
    for p in range(9):
        out[p]=solve(12,p,9);print(p,{k:v for k,v in out[p].items() if k!='rows'},flush=True)
        (D/'optimal-inverters.json').write_text(json.dumps(out))

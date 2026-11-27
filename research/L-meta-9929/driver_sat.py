"""The 27 public chain rows. One NOT, constrained complement at that gate and driver at output."""
from pathlib import Path
from itertools import combinations,permutations
from shutil import which
import subprocess,json,sys
from check_rup import verify
D=Path(__file__).resolve().parent
def constraints():
    req={}
    for perm in permutations(range(6)):
        chain=[0]
        for i in perm:chain.append(chain[-1]+(1<<i))
        if [int((x&7)>(x>>3)) for x in chain]!=[0,1,0,1,0,1,0]:continue
        for i,x in enumerate(chain):
            pair=(int(i<4),int(i in [2,3,6]))
            assert x not in req or req[x]==pair
            req[x]=pair
    assert len(req)==27
    return req
def problem(slots,inversion,fix=None):
    req=constraints();rows=sorted(req);length=len(rows)
    clauses=[];counter=0
    def fresh(n):
        nonlocal counter
        counter+=n;return list(range(counter-n+1,counter+1))
    def one(items):
        clauses.append(items);clauses.extend([-a,-b] for a,b in combinations(items,2))
    wires=[fresh(length) for _ in range(8+slots)]
    # Six raw inputs followed by the two free constants.
    for r,x in enumerate(rows):
        for j in range(8):
            y=wires[j][r];value=(x>>j&1) if j<6 else int(j==7)
            clauses.append([y if value else -y])
    for i in range(slots):
        out=wires[8+i];a,b=fresh(length),fresh(length)
        choices=[]
        for port,values in enumerate([a] if i==inversion else [a,b]):
            sel=fresh(8+i);one(sel);choices.append(sel)
            for s,wire in zip(sel,wires):
                for v,t in zip(values,wire):clauses.extend([[-s,-v,t],[-s,v,-t]])
        op=fresh(1)[0]
        if i!=inversion:
            for l,s in enumerate(choices[0]):
                for t in choices[1][:l]:clauses.append([-s,-t])
        for r,x in enumerate(rows):
            u,v,y=a[r],b[r],out[r]
            if i==inversion:clauses.extend([[-u,-y],[u,y],[y if req[x][0] else -y]])
            else:clauses.extend([[-op,-u,-v,y],[-op,u,-y],[-op,v,-y],[op,u,v,-y],[op,-u,y],[op,-v,y]])
            if i==slots-1:clauses.append([y if req[x][1] else -y])
        if fix:
            sym,l,r=fix[i]
            assert (sym=='not')==(i==inversion)
            if i!=inversion:
                l,r=sorted((l,r));clauses.extend([[op if sym=='and' else -op],[choices[1][r]]])
            clauses.append([choices[0][l]])
    return counter,clauses
def run(n,i,fix=None):
    name='positive' if fix else 'driver'+str(i)
    cnf=D/(name+'.cnf');proof=D/(name+'.lrat')
    nv,clauses=problem(n,i,fix)
    with cnf.open('w') as f:
        print('p cnf',nv,len(clauses),file=f)
        for c in clauses:print(*c,0,file=f)
    solver=which('cadical') or next((D.parent/'lean-runtime/toolchains').glob('*/bin/cadical'))
    code=subprocess.run([str(solver),'--lrat','--no-binary','-q','-t','180',str(cnf),str(proof)],stdout=subprocess.DEVNULL).returncode
    if code==20:return verify(cnf,proof)
    if fix and code==10:return 'SAT'
    return 'UNKNOWN' if code==0 else str(code)
if __name__=='__main__':
    # b0,b1,b2 majority followed by its complement. Second driver's
    # truth table is odd parity of b0,b1,b2 on all eight weights.
    control=[('and',3,4),('or',3,4),('and',9,5),('or',8,10),
             ('not',11,0),('or',9,5),('and',12,13),('and',8,5),('or',14,15)]
    assert run(9,4,control)=='SAT'
    print('nine-slot positive control passed',flush=True)
    cert={}
    for i in [0,1,2,3,6,7,4,5]:
        cert[i]=run(8,i);print(i,cert[i],flush=True)
        (D/'driver-results.json').write_text(json.dumps(cert))

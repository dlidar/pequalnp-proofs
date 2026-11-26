"""Sampled exact synthesis for assigned shard 9. Validate every model on 1,024 rows."""
import fcntl,itertools,json,random,subprocess,time
from pathlib import Path
w=Path(__file__).resolve().parent
solver=next((w.parent/'lean-runtime/toolchains').glob('*/bin/cadical'))
tri=[(0,1,4),(0,2,5),(0,3,6),(1,2,7),(1,3,8),(2,3,9),(4,5,7),(4,6,8),(5,6,9),(7,8,9)]
def target(r):
    return any(all(r>>i&1 for i in t) for t in tri)
def evaluate(g,r):
    v=[bool(r>>i&1) for i in range(10)]
    for op,i,j in g:
        v.append((v[i] and v[j]) if op=='and' else ((v[i] or v[j]) if op=='or' else not v[i]))
    return v[-1]
def encode(rows,targets,count,limits,fix=None):
    clauses=[];nv=0
    def var():
        nonlocal nv
        nv+=1
        return nv
    def one(x):
        clauses.append(x[:])
        clauses.extend([-a,-b] for a,b in itertools.combinations(x,2))
    def ranged(bits,lo,hi):
        # D[i,j] means at least j of the first i selected.
        t,f=var(),var()
        clauses.extend([[t],[-f]])
        dp=[t]+[f]*(hi+1)
        for bit in bits:
            nxt=[t]
            for j in range(1,hi+2):
                h,p,c=dp[j],dp[j-1],var()
                clauses.extend([[-h,c],[-p,-bit,c],[-c,h,p],[-c,h,bit]])
                nxt.append(c)
            dp=nxt
        clauses.extend([[dp[lo]],[-dp[hi+1]]])
    wires=[[var() for _ in rows] for i in range(10)]
    for i,wv in enumerate(wires):
        clauses.extend([z if r>>i&1 else -z] for r,z in zip(rows,wv))
    desc=[]
    for k in range(count):
        ops=[var() for _ in range(3)];one(ops)
        aop,oop,nop=ops
        choices=[];values=[]
        for side in range(2):
            choice=[var() for _ in wires];one(choice)
            val=[var() for _ in rows]
            for s,ws in zip(choice,wires):
                for x,y in zip(val,ws):
                    clauses.extend([[-s,-x,y],[-s,x,-y]])
            choices.append(choice);values.append(val)
        for i,x in enumerate(choices[0]):
            for j in range(i):
                clauses.append([nop,-x,-choices[1][j]])
        clauses.append([-nop,choices[1][0]])
        z=[var() for _ in rows];wires.append(z)
        for x,y,o in zip(*values,z):
            clauses.extend([[-aop,-x,-y,o],[-aop,x,-o],[-aop,y,-o],
                [-oop,x,y,-o],[-oop,-x,o],[-oop,-y,o],[-nop,-x,-o],[-nop,x,o]])
        if fix:
            kind,i,j=fix[k]
            if kind!='not': i,j=sorted([i,j])
            else:j=0
            clauses.extend([[ops[['and','or','not'].index(kind)]],[choices[0][i]],[choices[1][j]]])
        desc.append((ops,choices))
    ranged([d[0][0] for d in desc],*limits[0])
    ranged([d[0][2] for d in desc],*limits[1])
    clauses.extend([z if t else -z] for t,z in zip(targets,wires[-1]))
    p=w/'synthesis.cnf'
    with p.open('w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        f.writelines(' '.join(map(str,c))+' 0\n' for c in clauses)
    return p,desc
def solve(p,t):
    with (w/'solver.log').open('w') as f:
        return subprocess.run([str(solver),'-q','-t',str(t),str(p)],stdout=f).returncode
def model(desc):
    s={int(x) for line in (w/'solver.log').read_text().splitlines() if line.startswith('v ') for x in line[2:].split()}
    return [(['and','or','not'][next(i for i,x in enumerate(ops) if x in s)],*[next(i for i,x in enumerate(c) if x in s) for c in cs]) for ops,cs in desc]
def run():
    ctrl=[('not',0,0),('not',10,0)]+[('and' if i<8 else 'or',(10+i)%10,11+i) for i in range(18)]
    rows=list(range(0,1024,11));out=[evaluate(ctrl,r) for r in rows]
    limits=((6,10),(2,2))
    assert solve(encode(rows,out,20,limits,ctrl)[0],20)==10
    assert solve(encode(rows,[not out[0]]+out[1:],20,limits,ctrl)[0],20)==20
    print('Shard positive and corrupted controls passed',flush=True)
    rows=[sum(1<<i for i in t) for t in tri]
    rows.extend(r for r in range(1024) if not target(r) and all(target(r|1<<i) for i in range(10) if not r>>i&1))
    rows=list(dict.fromkeys(rows+[0,1023]+[1<<i for i in range(10)]))
    start=time.monotonic()
    while time.monotonic()-start<1200 and not (w/'stop').exists():
        p,desc=encode(rows,[target(r) for r in rows],20,limits)
        print('searching',len(rows),'rows',flush=True)
        code=solve(p,max(1,int(1200+start-time.monotonic())))
        if code!=10:
            verdict={0:'UNKNOWN',20:'UNSAT on normalized 20-slot sample encoding'}.get(code,'solver error '+str(code))
            (w/'outcome').write_text(verdict);print(verdict,flush=True);return
        gates=model(desc)
        assert sum(op=='not' for op,_,_ in gates)==2 and 6<=sum(op=='and' for op,_,_ in gates)<=10
        bad=[r for r in range(1024) if evaluate(gates,r)!=target(r)]
        assert not (set(bad)&set(rows))
        if not bad:
            (w/'witness.json').write_text(json.dumps(gates));(w/'outcome').write_text('truth-table witness');return
        rows.extend(random.Random(len(rows)).sample(bad,min(16,len(bad))))
    (w/'outcome').write_text('UNKNOWN')
if __name__=='__main__':
    with (w/'solver.lock').open('a') as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
        run()

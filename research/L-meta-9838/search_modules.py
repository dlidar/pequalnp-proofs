"""Synthesize replacements for groups of stars on the exact incidence graph."""
import itertools as it,json,os,random,shutil,subprocess,time
from pathlib import Path

SOURCE = Path(__file__).resolve().parent
W = Path(os.environ.get('PNP_OUTPUT', SOURCE / 'module-search')).resolve()
W.mkdir(parents=True, exist_ok=True)
E = json.loads((SOURCE / 'edges.json').read_text())
SOLVER = os.environ.get('CADICAL') or shutil.which('cadical') or 'cadical'

def running():
    return not (W / 'stop').exists()

def grouped(side,centers):
    ee=E if side==0 else [(b,a) for a,b in E]
    blocks={}
    for v in sorted({b for a,b in ee}):
        mask=sum(1<<i for i,u in enumerate(centers) if (u,v) in edge_sets[side])
        if mask:blocks.setdefault(mask,[]).append(v)
    return blocks
edge_sets=[set(map(tuple,E)),{(b,a) for a,b in E}]
def representatives():
    result={}
    for k in range(2,5):
        perms=list(it.permutations(range(k)))
        renames=[[sum(1<<p[i] for i in range(k) if m>>i&1) for m in range(1<<k)] for p in perms]
        for side in (0,1):
            for centers in it.combinations(range(side*20,side*20+20),k):
                blocks=grouped(side,centers)
                sig=min(tuple(sorted(ren[m] for m in blocks)) for ren in renames)
                result.setdefault((k,sig),(side,centers,blocks))
    return list(result.values())

def build_stars(k,masks):
    gates=[]
    def gate(op,a,b):
        gates.append((op,a,b));return k+len(masks)+len(gates)-1
    def reduce_or(q):
        a=q[0]
        for b in q[1:]:a=gate('or',a,b)
        return a
    terms=[gate('and',i,reduce_or([k+j for j,m in enumerate(masks) if m>>i&1])) for i in range(k)]
    return gates,reduce_or(terms)

def truth(n,gates,out):
    rows=1<<n; allm=(1<<rows)-1
    # The j-th column alternates blocks of 2^j zeros and ones.
    t=[(allm//((1<<(2*(1<<j)))-1))*(((1<<(1<<j))-1)<<(1<<j)) for j in range(n)]
    for op,a,b in gates:
        assert 0<=a<len(t) and 0<=b<len(t)
        t.append((t[a]&t[b]) if op=='and' else (t[a]|t[b]) if op=='or' else (allm^t[a]))
    return t[out]
def target_word(k,masks):
    n=k+len(masks)
    return sum(1<<x for x in range(1<<n) if any((x>>(k+j)&1) and (x&m) for j,m in enumerate(masks)))
def samples(k,masks,t):
    n=k+len(masks);allm=(1<<n)-1
    rows={0,allm}
    for i in range(n):rows.update((1<<i,allm^(1<<i)))
    for j,m in enumerate(masks):
        for i in range(k):rows.add((1<<i)|(1<<(k+j)))
    for points in range(1<<k):
        avail=sum(1<<(k+j) for j,m in enumerate(masks) if not points&m)
        rows.add(points|avail)
    rng=random.Random(9838)
    rows.update(rng.randrange(allm+1) for _ in range(20))
    return sorted(rows)
def synth(n,count,tests,target,limit,force=None,free=False,certificate=None):
    width=n+2 if free else n
    clauses=[];nv=0
    def new():
        nonlocal nv
        nv+=1;return nv
    def choose(m):
        v=[new() for _ in range(m)];clauses.append(v)
        clauses.extend([-a,-b] for a,b in it.combinations(v,2))
        return v
    ops=[];aa=[];bb=[]
    for i in range(count):
        op=choose(3);a=choose(width+i);b=choose(width+i);ops.append(op);aa.append(a);bb.append(b)
        for x in range(width+i):
            for y in range(x):clauses.append([-a[x],-b[y]])
            clauses.append([-op[2],-a[x],b[x]])
        if force:
            kind,x,y=force[i];x,y=sorted((x,y));j=['and','or','not'].index(kind)
            clauses.extend([[op[j]],[a[x]],[b[y]]])
    for x in tests:
        v=[new() for _ in range(n)]
        clauses.extend([[w if x>>i&1 else -w] for i,w in enumerate(v)])
        if free:
            lo,hi=new(),new();v.extend([lo,hi]);clauses.extend([[-lo],[hi]])
        for i,(op,a,b) in enumerate(zip(ops,aa,bb)):
            p,q,z=new(),new(),new()
            for selectors,u in [(a,p),(b,q)]:
                for s,w in zip(selectors,v):clauses.extend([[-s,-u,w],[-s,u,-w]])
            clauses.extend([[-op[0],-p,-q,z],[-op[0],p,-z],[-op[0],q,-z],
                            [-op[1],p,q,-z],[-op[1],-p,z],[-op[1],-q,z],
                            [-op[2],p,z],[-op[2],-p,-z]])
            v.append(z)
        clauses.append([v[-1] if target>>x&1 else -v[-1]])
    cnf=certificate.with_suffix('.cnf') if certificate else W/'module.cnf'
    with cnf.open('w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n');f.writelines(' '.join(map(str,c))+' 0\n' for c in clauses)
    cmd=[str(SOLVER),'-t',str(limit)]
    cmd+=['--no-binary','--lrat',str(cnf),str(certificate)] if certificate else [str(cnf)]
    res=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=limit+20)
    if res.returncode==20:return 'UNSAT',None
    if res.returncode!=10:return 'UNKNOWN',None
    pos={int(t) for l in res.stdout.splitlines() if l.startswith('v ') for t in l[2:].split() if int(t)>0}
    def chosen(v):
        indices=[i for i,x in enumerate(v) if x in pos];assert len(indices)==1;return indices[0]
    return 'SAT',[(['and','or','not'][chosen(k)],chosen(a),chosen(b)) for k,a,b in zip(ops,aa,bb)]

def lift(side,centers,blocks,small):
    gates=[]
    def put(op,a,b):
        assert max(a,b)<40+len(gates)
        gates.append((op,a,b));return 39+len(gates)
    def fold(xs):
        u=xs[0]
        for v in xs[1:]:u=put('or',u,v)
        return u
    vals=list(centers)+[fold(blocks[m]) for m in sorted(blocks)]
    for op,a,b in small:vals.append(put(op,vals[a],vals[b]))
    roots=[vals[-1]]
    for u in range(side*20,side*20+20):
        if u not in centers:roots.append(put('and',u,fold(sorted(v for i,v in edge_sets[side] if i==u))))
    out=fold(roots);assert len(gates)==113
    (W/'witness.json').write_text(json.dumps(dict(gates=gates,out=out,side=side,centers=centers,blocks=blocks,small=small)))
def main():
    if not running():return
    reps=representatives()
    assert synth(3,1,list(range(8)),0b10000000,5)[0]=='UNSAT'
    # Independently compare a formula with a witness extracted from its pinned CNF.
    for k,m in [(2,[1,2,3]),(3,[1,2,3,4,5,6])]:
        g,o=build_stars(k,m);t=target_word(k,m);n=k+len(m)
        assert truth(n,g,o)==t
        st,h=synth(n,len(g),samples(k,m,t),t,6,force=g)
        assert st=='SAT' and truth(n,h,n+len(h)-1)==t
    print('controls passed, classes',len(reps),flush=True)
    deadline=time.monotonic()+1150
    # Spread the first pass across every isomorphism class before deeper retries.
    for budget in (8,30,90):
        for side,c,b in reps:
            if time.monotonic()>=deadline or not running():return
            k=len(c);ms=sorted(b);n=k+len(ms);t=target_word(k,ms);g,o=build_stars(k,ms)
            assert truth(n,g,o)==t
            key=str(k)+'_'+'.'.join(map(str,ms))
            if (W/('local-unsat-'+key)).exists():continue
            tests=samples(k,ms,t)
            for rnd in range(4):
                if not running():return
                st,h=synth(n,len(g)-1,tests,t,budget)
                print('local module',key,'gates',len(g)-1,st,'samples',len(tests),flush=True)
                if st!='SAT':
                    if st=='UNSAT':(W/('local-unsat-'+key)).write_text('solver result on this restricted module only')
                    break
                actual=truth(n,h,n+len(h)-1)
                assert all(((actual^t)>>x&1)==0 for x in tests)
                if actual==t:
                    lift(side,c,b,h);print('candidate exact on module',flush=True);return
                delta=actual^t
                for _ in range(10):
                    if not delta:break
                    bit=delta&-delta;tests.append(bit.bit_length()-1);delta-=bit
if __name__=='__main__':main()

"""Search for a circuit strictly below star-cover cost on six residual 4+4 graphs."""
from pathlib import Path
from itertools import combinations
import fcntl,json,subprocess,shutil,os
from small import classes
w=Path(__file__).resolve().parent
def ref(edges):
    masks=[(1<<i)|(1<<j) for i,j in edges]
    cover=min((t for t in range(256) if all(t&x for x in masks)),key=int.bit_count)
    groups={};g=[]
    for i,j in edges:
        owner,leaf=(i,j) if cover>>i&1 else (j,i);groups.setdefault(owner,[]).append(leaf)
    def add(op,a,b):g.append((op,a,b));return 7+len(g)
    roots=[]
    for v,leaves in groups.items():
        a,*tail=leaves
        for b in tail:a=add(False,a,b)
        roots.append(add(True,v,a))
    a,*tail=roots
    for b in tail:a=add(False,a,b)
    assert a==7+len(g)
    return g
def run(mask,gs,rows,target,fixed,limit):
    k=0;clauses=[]
    def var():
        nonlocal k;k+=1;return k
    def one(lst):
        clauses.append(lst);clauses.extend([-a,-b] for a,b in combinations(lst,2))
    values=[[var() for _ in rows] for _ in range(gs+8)]
    for j in range(8):clauses.extend([z if x>>j&1 else -z] for x,z in zip(rows,values[j]))
    sels=[]
    for i in range(8,len(values)):
        op=var();ss=[];vv=[]
        for h in range(2):
            s=[var() for _ in range(i)];one(s);ss.append(s);u=[var() for _ in rows];vv.append(u)
            for c,old in zip(s,values[:i]):
                for a,b in zip(old,u):clauses.extend([[-c,-a,b],[-c,a,-b]])
        # Any commutative binary gate can be sorted.
        clauses.extend([-ss[0][u],-ss[1][v]] for u in range(i) for v in range(u))
        for a,b,z in zip(*vv,values[i]):
            clauses.extend([[-op,-a,-b,z],[-op,a,-z],[-op,b,-z],[op,a,b,-z],[op,-a,z],[op,-b,z]])
        sels.append((op,ss))
        if fixed:
            typ,a,b=fixed[i-8];a,b=sorted((a,b));clauses.extend([[op if typ else -op],[ss[0][a]],[ss[1][b]]])
    for x,z in zip(rows,values[-1]):clauses.append([z if target[x] else -z])
    prefix=w/(str(mask)+('-control' if fixed else '-bounded'));cnf=prefix.with_suffix('.cnf')
    with cnf.open('w') as f:
        f.write(f'p cnf {k} {len(clauses)}\n');f.writelines(' '.join(map(str,c))+' 0\n' for c in clauses)
    cmd=[os.environ.get('CADICAL') or shutil.which('cadical') or 'cadical','-q','-t',str(limit),cnf]
    r=subprocess.run(cmd,stdout=subprocess.PIPE,text=True)
    if r.returncode==10:
        model={int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:]}
        gates=[(op in model,*[next(j for j,c in enumerate(s) if c in model) for s in ss]) for op,ss in sels]
        for x in range(256):
            b=[bool(x>>i&1) for i in range(8)]
            for op,i,j in gates:b.append((b[i] and b[j]) if op else (b[i] or b[j]))
            assert b[-1]==target[x]
        return 'SAT',gates
    return {0:'UNKNOWN',20:'UNSAT'}[r.returncode],None
if __name__=='__main__':
    lock=(w/'solver.lock').open('a');fcntl.flock(lock,6)
    for item in classes():
        m=item['mask'];p=w/(str(m)+'.outcome')
        if p.exists():continue
        ed=[(i,j+4) for i,j in item['edges']];target=[any((x>>i)&(x>>j)&1 for i,j in ed) for x in range(256)]
        positives={(1<<i)|(1<<j) for i,j in ed};rows=sorted(positives|{x for x in range(256) if not target[x] and all(target[x|1<<j] for j in range(8) if not x>>j&1)})
        g=ref(ed);assert len(g)==item['star_gates'] and run(m,len(g),rows,target,g,20)[0]=='SAT'
        print(m,'control',len(g),'passed all 256; searching',len(g)-1,'gates on',len(rows),'boundary tests',flush=True)
        status,cand=run(m,len(g)-1,rows,target,None,120)
        if cand:(w/'witness.json').write_text(json.dumps(dict(graph=item,gates=cand)))
        p.write_text(status);print(m,status,flush=True)
        if cand:break
    (w/'bounded-finished').touch()

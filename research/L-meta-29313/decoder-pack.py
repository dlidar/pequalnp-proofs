from labels import *
import subprocess,random
solver=subprocess.Popen([p/'smalldec'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
rng=random.Random(29313);src=p/'decoder-packs.json';res=json.loads(src.read_text()) if src.exists() else {}
def lower(P,N,h):
    ins=[v+256*(1-((h>>v)&1)) for v in P+N]
    solver.stdin.write(' '.join(map(str,[len(P),len(N)]+ins))+'\n');solver.stdin.flush()
    return int(solver.stdout.readline())
for trial in range(14):
 for k,op,i,j,h in cases:
    key=hex(h)
    if res.get(key,{}).get('bound',0)==15:continue
    P,N=lift(h)
    if trial==0 and len(P)+len(N)<=21 and len(P)<=15:
        a,b=P,N
    else:
        a=sorted(rng.sample(P,min(len(P),12)));b=sorted(rng.sample(N,min(len(N),7)))
    val=lower(a,b,h)
    if val>res.get(key,{}).get('bound',0):res[key]=dict(P=a,N=b,bound=val)
    if val==15:print(op,i,j,15,flush=True)
    temp=src.with_suffix('.tmp');temp.write_text(json.dumps(res));temp.replace(src)
 if (p/'lost').exists() or (p/'stop').exists():break
solver.stdin.close();solver.wait()

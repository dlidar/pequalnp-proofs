from itertools import permutations
def f(w):return (w&7)>(w>>3)
def analyze():
    chains=[];zero=set();one=set()
    for perm in permutations(range(6)):
        chain=[0]
        for j in perm: chain.append(chain[-1]|1<<j)
        drops=[i for i in range(6) if f(chain[i]) and not f(chain[i+1])]
        if len(drops)==3:
            chains.append(chain);i=drops[1]
            zero.add(chain[i]);one.add(chain[i+1])
    forced0={w for w in range(64) if any(w|z==z for z in zero)}
    forced1={w for w in range(64) if any(w|z==w for z in one)}
    a=sorted(z for z in zero if all(z==v or z|v!=v for v in zero))
    b=sorted(z for z in one if all(z==v or z|v!=z for v in one))
    print('chains',len(chains),'forced',len(forced0),len(forced1),'max0',a,'min1',b,'undetermined',sorted(set(range(64))-forced0-forced1))
    return chains,forced0,forced1
if __name__=='__main__':analyze()
def enc(rows):return sum(1<<i for i in rows)
def costs():
    from itertools import combinations
    chains,z,o=analyze();neg,pos=enc(z),enc(o);raw=tuple(enc(w for w in range(64) if w>>j&1) for j in range(6))
    states={frozenset(raw):()};fits={}
    for k in range(1,5):
        later={}
        for s,gates in states.items():
            for a,b in combinations(s,2):
                for op,v in [('and',a&b),('or',a|b)]:
                    if v in s:continue
                    g=gates+((op,a,b),)
                    if not v&neg and v&pos==pos:fits.setdefault(v,g)
                    if k<4:later.setdefault(s|{v},g)
        states=later
        print(k,len(states),len(fits),flush=True)
    return raw,fits
if __name__=='__main__':
 raw,fits=costs()
 for f in fits:print(hex(f))

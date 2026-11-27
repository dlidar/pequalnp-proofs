"""Every four-coordinate restriction with fixed prefix values and a P4 edge function."""
import itertools,json
from pathlib import Path
p=Path(__file__).parent
terms=[(0,4,8),(0,5,7),(1,3,8),(1,5,6),(2,3,7),(2,4,6)]
def fn(x):return any(all(x>>j&1 for j in t) for t in terms)
def images():
    result=[]
    base=[x for x in range(16) if ((x&5)==5 or (x&10)==10 or (x&6)==6)]
    for free in itertools.combinations(range(9),4):
        fixed=sorted(set(range(9))-set(free))
        for mask in range(32):
            pre=sum(1<<j for k,j in enumerate(fixed) if mask>>k&1)
            if not all((pre&pair==pair) or (sum(1<<j for j in free)|pre)&pair != pair for pair in [3,288]):continue
            for order in itertools.permutations(free):
                xs=[pre|sum(1<<j for k,j in enumerate(order) if x>>k&1) for x in range(16)]
                if all(fn(u)==(x in base) for x,u in enumerate(xs)):
                    result.append((pre,order));break
    return result
if __name__=='__main__':
    results=images()
    print('P4 restrictions',len(results),'free sets',len({tuple(sorted(f)) for _,f in results}))
    print('number fixing each raw input',[sum(i not in f for _,f in results) for i in range(9)])
    (p/'restrictions.json').write_text(json.dumps(results))

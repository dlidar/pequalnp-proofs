"""Omitted-coordinate factors of the punctured Heawood edge predicate."""
from itertools import combinations
from verify_edits import EDGES
N=14
def counts():
    edges=[(1<<a)|(1<<b) for a,b in EDGES]
    truth=[any(x & edge == edge for edge in edges) for x in range(1<<N)]
    zeros=[x for x in range(1<<N) if not truth[x]]
    maximal=[x for x in zeros if all(x>>i&1 or truth[x|1<<i] for i in range(N))]
    def hit(t):
        return all(any(x>>i&1 for i in t) for x in maximal)
    pairs=[tuple(t) for i in range(N) for t in [(i,j) for j in range(i,N)]]
    profile={t:sum(all(truth[x|1<<i] for i in t) for x in zeros) for t in pairs}
    good=[t for t in combinations(range(N),3) if hit(t)]
    assert all(all(truth[x]==all(truth[x|1<<i] for i in t) for x in range(1<<N)) for t in good)
    return truth,maximal,profile,good
if __name__=='__main__':
    truth,maximal,profile,good=counts()
    print('maximal independent sets',len(maximal))
    print('pair error range',min(profile.values()),max(profile.values()))
    print('sharp pairs',[p for p,n in profile.items() if n==min(profile.values())])
    print('all feasible triples',good)

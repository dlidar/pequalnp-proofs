"""Count and index permitted partial pins using alternating cycles of two matchings."""
from collections import Counter
from functools import lru_cache
from math import comb

def cycles(perm):
    n = len(perm)
    assert sorted(perm) == list(range(n))
    inverse = {j: i for i, j in enumerate(perm)}
    unseen = set(range(n))
    while unseen:
        i = min(unseen)
        cycle = []
        while i in unseen:
            unseen.remove(i)
            cycle.extend([i, n+i])
            i = inverse[i]
        yield cycle

def increment(inventory, color, length):
    return tuple(sorted((*inventory, (color, length))))

def close_arc(inventory, first, first_digit, last, last_digit, length):
    return increment(inventory, 2*(last % 2) + (last_digit != first_digit), length-last+first)

@lru_cache(maxsize=4096)
def polynomial(n, inventory, free):
    result = {(0, 0): 2**free}
    for color, length in inventory:
        red = (length + (color//2 == 0))//2
        blue = length-red
        factor = [(a,b,comb(red,a)*comb(blue,b)) for a in range(red+1) for b in range(blue+1)
                  if (a+b)%2 == color%2]
        new = Counter()
        for (i,j),v in result.items():
            for a,b,c in factor:
                new[i+a,j+b] += v*c
        result = new
    return tuple(result.get((r,b),0) for r in range(n+1) for b in range(n+1))

def distributions(perm, allow):
    n = len(perm)
    assert len(allow) == 2*n
    done = Counter({((),0):1})
    for cycle in cycles(perm):
        active = {(inv,free,-1,0,-1,0):weight for (inv,free),weight in done.items()}
        for j,v in enumerate(cycle):
            new = Counter()
            for (inv,free,first,a,last,b),weight in active.items():
                for digit in range(3):
                    if not allow[v] & (1<<digit): continue
                    if digit == 0: key = inv,free,first,a,last,b
                    elif first == -1: key = inv,free,j,digit,j,digit
                    else:
                        ext = increment(inv, 2*(last%2)+(b!=digit), j-last)
                        key = ext,free,first,a,j,digit
                    new[key] += weight
            active = new
        done = Counter()
        for (inv,free,first,a,last,b),weight in active.items():
            if first == -1: key = increment(inv,0,len(cycle)),free+1
            else: key = close_arc(inv,first,a,last,b,len(cycle)),free
            done[key] += weight
    out = Counter()
    for (inv,free),weight in done.items():
        out[polynomial(n,inv,free)] += weight
    return out

def index(perm, allow, target, pin, ordinal):
    """Return fiber size, membership, rank for a member, and pin at an existing ordinal."""
    def count(permissions):
        return distributions(perm,permissions)[target]
    total = count(allow)
    member = all(mask & (1<<v) for mask,v in zip(allow,pin)) and count(
        tuple(mask & (1<<v) for mask,v in zip(allow,pin))) == 1
    def buckets(permissions, i):
        return [count(permissions[:i]+(permissions[i] & (1<<d),)+permissions[i+1:]) for d in range(3)]
    rank = 0
    constrained = allow
    if member:
        for i in reversed(range(len(allow))):
            rank += sum(buckets(constrained,i)[:pin[i]])
            constrained = constrained[:i]+(1<<pin[i],)+constrained[i+1:]
    result = None
    if 0 <= ordinal < total:
        constrained = allow
        for i in reversed(range(len(allow))):
            for d,weight in enumerate(buckets(constrained,i)):
                if ordinal < weight: break
                ordinal -= weight
            constrained = constrained[:i]+(1<<d,)+constrained[i+1:]
        result = tuple(v.bit_length()-1 for v in constrained)
    return total, bool(member), rank if member else None, result

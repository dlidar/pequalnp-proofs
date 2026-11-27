"""Compile a circuit with all inputs in the project's posted order."""
from inventory import increment, close_arc, polynomial

class Gates:
    def __init__(self, inputs):
        self.inputs = inputs
        self.program = []
        self.cache = {}
    def gate(self, op, a, b=None):
        if op != 'not':
            a,b = sorted((a,b))
            if a == b: return a
            if a <= 1:
                if op == 'and': return b if a else 0
                return 1 if a else b
        elif a <= 1: return 1-a
        key = (op,a,b)
        if key not in self.cache:
            self.cache[key] = self.inputs + len(self.program)
            self.program.append(key)
        return self.cache[key]
    def neg(self,a): return self.gate('not',a)
    def conj(self,a,b): return self.gate('and',a,b)
    def disj(self,a,b): return self.gate('or',a,b)
    def xor(self,a,b):
        if a == b: return 0
        return self.conj(self.disj(a,b),self.neg(self.conj(a,b)))
    def fold(self,op,bits):
        ans = int(op=='and')
        for bit in bits: ans = self.gate(op,ans,bit)
        return ans
    def mask(self,word,c): return tuple(self.conj(x,c) for x in word)
    def add(self,a,b):
        result=[]; carry=0
        for x,y in zip(a,b):
            v=self.xor(x,y)
            result.append(self.xor(v,carry))
            carry=self.disj(self.conj(x,y),self.conj(v,carry))
        return tuple(result)
    def subtract(self,a,b):
        result=[]; borrow=0
        for x,y in zip(a,b):
            v=self.xor(x,y)
            result.append(self.xor(v,borrow))
            borrow=self.disj(self.conj(self.neg(x),y),self.conj(self.neg(v),borrow))
        return tuple(result),borrow

def compile_circuit(n):
    m=2*n; width=4*n; hw=2*n+1
    inputs=2+n*n+6*n+(n+1)**2*hw+8*n
    g=Gates(inputs); at=2
    def wires(num):
        nonlocal at
        xs=tuple(range(at,at+num)); at+=num; return xs
    mat=[wires(n) for _ in range(n)]
    allow=list(zip(*(wires(m) for _ in range(3))))
    hist=[wires(hw) for _ in range((n+1)**2)]
    present,values,z=wires(m),wires(m),wires(width)
    assert at==inputs
    zero=(0,)*width; one=(1,)+zero[1:]
    # A cycle is processed exactly once, from its least left vertex.
    orbits=[]
    for root in range(n):
        here=tuple(int(i==root) for i in range(n)); walk=[]; running=1; ends=[]
        for length in range(1,n+1):
            walk.append(here)
            here=tuple(g.fold('or',(g.conj(mat[i][j],here[j]) for j in range(n))) for i in range(n))
            ends.append(g.conj(running,here[root]))
            running=g.conj(running,g.neg(g.fold('or',here[:root+1])))
        orbits.append((walk,ends,g.neg(g.fold('or',ends))))
    wanted={}
    def match(inv,free):
        h=polynomial(n,inv,free)
        if h not in wanted:
            wanted[h]=g.fold('and',(bit if (v>>j)&1 else g.neg(bit)
                for v,cells in zip(h,hist) for j,bit in enumerate(cells)))
        return wanted[h]
    def count(permissions):
        def accumulate(D,key,word):
            if word!=zero: D[key]=g.add(D[key],word) if key in D else word
        done={((),0):one}
        for walk,ends,skip in orbits:
            nxt={}
            for key,word in done.items(): accumulate(nxt,key,g.mask(word,skip))
            for length,cond in enumerate(ends,1):
                if cond==0: continue
                active={(inv,free,-1,0,-1,0):g.mask(word,cond) for (inv,free),word in done.items()
                        if sum(l for _,l in inv)+2*length<=m}
                for j in range(2*length):
                    allowed=[g.fold('or',(g.conj(bit,permissions[(j%2)*n+i][d])
                        for i,bit in enumerate(walk[j//2]))) for d in range(3)]
                    fresh={}
                    for state,word in active.items():
                        inv,free,first,a,last,b=state
                        for digit,ok in enumerate(allowed):
                            if not digit: key=state
                            elif first<0: key=inv,free,j,digit,j,digit
                            else: key=increment(inv,2*(last%2)+(digit!=b),j-last),free,first,a,j,digit
                            accumulate(fresh,key,g.mask(word,ok))
                    active=fresh
                for (inv,free,first,a,last,b),word in active.items():
                    if first<0: key=increment(inv,0,2*length),free+1
                    else: key=close_arc(inv,first,a,last,b,2*length),free
                    accumulate(nxt,key,word)
            done=nxt
        total=zero
        for (inv,free),word in done.items():
            total=g.add(total,g.mask(word,match(inv,free)))
        return total
    def restrict(row,chosen): return tuple(g.conj(a,b) for a,b in zip(row,chosen))
    num=count(allow)
    fixed=list(allow); select=list(allow); rank=zero; residual=z; pouts=[None]*m
    for i in reversed(range(m)):
        actual=(g.neg(present[i]),g.conj(present[i],g.neg(values[i])),g.conj(present[i],values[i]))
        def first_two(rows):
            return [count(rows[:i]+[restrict(rows[i],tuple(int(j==d) for j in range(3)))]+rows[i+1:])
                    for d in range(2)]
        a,b=first_two(fixed)
        rank=g.add(rank,g.add(g.mask(a,present[i]),g.mask(b,actual[2])))
        fixed[i]=restrict(fixed[i],actual)
        u,v=first_two(select)
        sub,low=g.subtract(residual,u)
        rest,mid=g.subtract(sub,v)
        chosen=(low,g.conj(g.neg(low),mid),g.conj(g.neg(low),g.neg(mid)))
        residual=tuple(g.fold('or',(g.conj(c,w[j]) for c,w in zip(chosen,(residual,sub,rest)))) for j in range(width))
        select[i]=restrict(select[i],chosen)
        pouts[i]=(g.neg(low),chosen[2])
    valid=count(fixed)[0]
    return g,(num,rank,valid,pouts)

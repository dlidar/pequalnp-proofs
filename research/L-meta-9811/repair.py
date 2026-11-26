"""Find the nearest single-gate repairs of two families of 24-slot circuits."""
from pathlib import Path
import json
from verify_edits import EDGES

WIDTH = 1 << 14
ALL = (1 << WIDTH) - 1
RAW = [sum(1 << x for x in range(WIDTH) if x & (1<<i)) for i in range(14)]
TARGET = 0
for a,b in EDGES:
    TARGET |= RAW[a] & RAW[b]

def output(gates, forced=None, value=0):
    values = RAW.copy()
    for j,(kind,a,b) in enumerate(gates):
        x,y = values[a],values[b]
        if j == forced: z = value
        elif kind == 'and': z = x & y
        elif kind == 'or': z = x | y
        elif kind == 'not': z = ALL ^ x
        else: raise ValueError(kind)
        values.append(z)
    return values

def star(edges,side):
    gates=[];terms=[]
    def emit(op,a,b):
        gates.append((op,a,b))
        return len(gates)+13
    for p in range(7*side,7*side+7):
        row=sorted(e[1-side] for e in edges if e[side]==p)
        z=row[0]
        for q in row[1:]: z=emit('or',z,q)
        terms.append(emit('and',p,z))
    z=terms[0]
    for t in terms[1:]:z=emit('or',z,t)
    return tuple(gates)

def bypass(gates,j,source):
    wire=14+j
    def adjust(v):
        return source if v==wire else v-int(v>wire)
    return tuple((op,adjust(a),adjust(b)) for k,(op,a,b) in enumerate(gates) if k!=j)

def seeds():
    for side in range(2):
        for e in sorted(EDGES):
            yield star(EDGES-{e},side)
        full=star(EDGES,side)
        for j,(_,a,b) in enumerate(full[:-1]):
            for source in (a,b):
                yield bypass(full,j,source)

def optimize():
    best=WIDTH; checked=0; saved=None
    for gates in sorted(set(seeds())):
        wires=output(gates)
        for j in range(len(gates)):
            out0=output(gates,j,0)[-1]; out1=output(gates,j,ALL)[-1]
            sensitive=out0^out1
            need=(TARGET^out0)&sensitive
            fixed=((TARGET^out0)&(ALL^sensitive)).bit_count()
            if fixed>=best: continue
            for a,x in enumerate(wires[:14+j]):
                for b,y in enumerate(wires[:a+1]):
                    ops=[('and',x&y),('or',x|y)]
                    if a==b:ops.append(('not',ALL^x))
                    for op,value in ops:
                        checked+=1
                        error=fixed+((value&sensitive)^need).bit_count()
                        if error>=best:continue
                        saved=list(gates);saved[j]=(op,a,b)
                        result=output(saved)[-1]
                        misses=(TARGET & (ALL^result)).bit_count()
                        extra=(result & (ALL^TARGET)).bit_count()
                        assert error==misses+extra
                        print(error,misses,extra,flush=True)
                        best=error
                        Path(__file__).with_name('best-repair.json').write_text(json.dumps({
                            'false_negatives':misses, 'false_positives':extra, 'gates':saved}))
                        if best==0:return
    print('complete',len(set(seeds())),'seeds',checked,'unpruned replacements',best,flush=True)
if __name__=='__main__':optimize()

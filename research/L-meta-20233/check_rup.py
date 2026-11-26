"""Verify text LRAT unit-propagation chains from DIMACS independently of the solver.

Only certified RUP additions are supported. Other proof steps raise an error.
A successful return requires an empty clause in the input or a verified derivation.
"""
from pathlib import Path
import sys

def verify(cnf, proof):
    clauses={}
    count=None
    with cnf.open() as stream:
        for line in stream:
            words=line.split()
            if not words or words[0]=='c':continue
            if words[0]=='p':
                if count is not None or len(words)!=4 or words[1]!='cnf':
                    raise ValueError('bad header')
                nv,count=map(int,words[2:])
                continue
            row=list(map(int,words))
            if count is None or row[-1]!=0 or any(x==0 or abs(x)>nv for x in row[:-1]):
                raise ValueError('bad input clause')
            clauses[len(clauses)+1]=tuple(set(row[:-1]))
    if len(clauses)!=count:raise ValueError('input clause count mismatch')
    if () in clauses.values():return 0
    additions=0
    largest=count
    with proof.open() as stream:
        for line in stream:
            w=line.split()
            if not w or w[0]=='c':continue
            if len(w)>=3 and w[1]=='d':
                if w[-1]!='0':raise ValueError('bad deletion')
                for cid in w[2:-1]:clauses.pop(int(cid),None)
                continue
            cid=int(w[0]);end=w.index('0',1)
            if cid<=largest or w[-1]!='0': raise ValueError('invalid proof index')
            largest=cid
            clause=set(map(int,w[1:end]))
            if any(abs(lit)>nv or lit==0 for lit in clause):raise ValueError('invalid variable')
            # Assume the proposed clause false. The hinted clauses must then
            # force a contradiction, so every model of the database satisfies it.
            true={-lit for lit in clause}
            contradictory=any(lit in true for lit in clause)
            if not contradictory:
                for hint in w[end+1:-1]:
                    idx=int(hint)
                    if idx<=0:raise ValueError('unsupported RAT hint')
                    old=clauses[idx]
                    if any(lit in true for lit in old):raise ValueError('satisfied hint')
                    unset=[lit for lit in old if -lit not in true]
                    if not unset:
                        contradictory=True
                        break
                    if len(unset)!=1:raise ValueError('non-unit hint')
                    true.add(unset[0])
            if not contradictory:raise ValueError('no contradiction for clause '+str(cid))
            additions+=1
            if not clause:return additions
            clauses[cid]=tuple(clause)
    raise ValueError('no empty clause proved')

if __name__=='__main__':
    n=verify(Path(sys.argv[1]),Path(sys.argv[2]))
    print(f'Empty clause verified after {n} additions.')

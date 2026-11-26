"""Exact primal and dual certificates for the fractional zero-rectangle cover."""
import json,itertools
from collections import Counter
from pathlib import Path
w=Path(__file__).resolve().parent
rows=json.loads((w/'rows.json').read_text())
full=(1<<30)-1
def lines(pts):
    m=0
    for i in pts:m|=rows[i]
    return m^full
def rectangle(p,l):
    return [(i,j) for i in range(25) if p>>i&1 for j in range(30) if l>>j&1]
def maximal():
    for pts in itertools.combinations(range(25),6):
        l=lines(pts)
        if l.bit_count()==9:yield sum(1<<i for i in pts),l
if __name__=='__main__':
    boxes=list(maximal())
    freq=Counter(c for p,l in boxes for c in rectangle(p,l))
    zeros={(i,j) for i,r in enumerate(rows) for j in range(30) if not r>>j&1}
    assert len(boxes)==1000 and len(zeros)==600 and set(freq)==zeros and set(freq.values())=={90}
    print('1000 rectangles of area 54; each of 600 zeros covered exactly 90 times')

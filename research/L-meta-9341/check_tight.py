"""Replay a branching certificate, checking every eligible rectangle at each node."""
from check_duals import *
def run():
 bs=independent_boxes();base=[(i,j) for i,j in product(range(3),range(21)) if not rows[i]>>j&1]
 for m,_,w,cap,total in json.loads((D/'all-residual-duals.json').read_text()):
  if 8*cap<total:continue
  reps=[pair for j,pair in enumerate(base) if not (m>>j&1)]
  cells=[((i+k)%21,(j+k)%21) for i,j in reps for k in range(0,21,3)]
  weights=[z for z in w for _ in range(7)]
  layers=[sum(1<<i for i,v in enumerate(weights) if v>=z) for z in range(1,max(weights)+1)]
  def value(s):return sum((s&L).bit_count() for L in layers)
  bits=sorted({sum(1<<i for i,(r,c) in enumerate(cells) if a>>r&1 and b>>c&1) for a,b in bs})
  assert value((1<<len(cells))-1)==total and max(map(value,bits))==cap
  choices=[[m for m in bits if m>>i&1 and value(m)+7*cap>=total] for i in range(len(cells))]
  trace=json.loads((D/f'branch-cells-{m}.json').read_text());n=0
  def replay(uncovered,slots):
   nonlocal n
   assert uncovered
   if slots==0:return
   point=trace[n];n+=1
   assert 0<=point<len(cells) and uncovered>>point&1
   for rect in choices[point]:
    rem=uncovered&~rect
    if value(rem)<=(slots-1)*cap:replay(rem,slots-1)
  replay((1<<len(cells))-1,8)
  assert n==len(trace)
  print(hex(m),n,'complete nodes independently checked',flush=True)
if __name__=='__main__':run()

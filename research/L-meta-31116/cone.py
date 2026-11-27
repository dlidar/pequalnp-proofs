"""Build the minimal positive and maximal negative rows for fixed inverter inputs."""
from pathlib import Path
from itertools import combinations
from upper import target
p=Path(__file__).resolve().parent
def problem(g):
 def state(x):
  w=[x>>j&1 for j in range(8)]
  for op,a,b in g:w.append(w[a]&w[b] if op=='a' else w[a]|w[b])
  w.append(1-w[-1])
  return sum(t<<j for j,t in enumerate(w))
 signatures=[state(x) for x in range(256)]
 positive=[x for x in range(256) if target(x)]
 negative=[x for x in range(256) if not target(x)]
 P=[x for x in positive if not any(y!=x and signatures[y]&signatures[x]==signatures[y] for y in positive)]
 N=[x for x in negative if not any(y!=x and signatures[y]&signatures[x]==signatures[x] for y in negative)]
 assert len(P)+len(N)<63
 labels=[sum((signatures[x]>>j&1)<<k for k,x in enumerate(P+N)) for j in range(9+len(g))]
 return P,N,labels
def write(name,g):
 P,N,labels=problem(g)
 (p/name).write_text(f'{len(P)} {len(N)} {len(labels)}\n'+' '.join(map(str,labels))+'\n')
if __name__=='__main__':
 for i,j in combinations(range(8),2):
  for op in 'ao':write(f'one-{i}{j}-{op}.task',[(op,i,j)])

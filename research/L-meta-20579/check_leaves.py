"""Independently check the raw-leaf lower bound with integer arithmetic."""
from pathlib import Path
import json
p=Path(__file__).resolve().parent
cert=json.loads((p/'leafweights.json').read_text());r=cert['rows'];scale=cert['unit']
assert r==json.loads((p/'weights.json').read_text())['rows'] and type(scale) is int and scale>0
w=[[0]*32 for _ in r]
for u,v,z in cert['weights']:
 assert r[u]>>v&1 and z>0 and w[u][v]==0
 w[u][v]=z
columns=[sum(1<<u for u,row in enumerate(r) if row>>v&1) for v in range(32)]
inter={(1<<32)-1}
for c in columns:inter.update(x&c for x in tuple(inter))
blocks=checks=0
for rs in inter-{0}:
 cs=sum(1<<v for v,c in enumerate(columns) if c&rs==rs)
 if not cs:continue
 blocks+=1
 U=[u for u in range(32) if rs>>u&1];V=[v for v in range(32) if cs>>v&1]
 transpose=len(U)>len(V)
 if transpose:U,V=V,U
 # Enumerate *all* subsets of the shorter side, maximize over the other side.
 for mask in range(1,1<<len(U)):
  selected=[u for j,u in enumerate(U) if mask>>j&1]
  gain=sum(max(0,sum((w[v][u] if transpose else w[u][v]) for u in selected)-scale) for v in V)
  assert gain<=scale*len(selected)
  checks+=1
total=sum(map(sum,w));assert total==cert['total']
print(blocks,'maximal boxes,',checks,'subset checks,',total,'/',scale,'forces',(total+scale-1)//scale,'raw leaves')

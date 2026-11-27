from cutwidth import *
def cert(t,d):
 pts,adj=problem(t);k=d['width']-1
 if d['clique']:return None
 ids=list(range(len(pts)))
 def adjfor(ids):
  return [sum(1<<j for j,v in enumerate(ids) if adj[u]>>v&1) for u in ids]
 for u in list(ids):
  smaller=[v for v in ids if v!=u]
  if color(adjfor(smaller),k) is None:ids=smaller
 a=adjfor(ids);n=len(a);start=clique(a,k);assert start
 states=[-1]*n
 for i,u in enumerate(start):states[u]=i
 def trace():
  U=[i for i,v in enumerate(states) if v<0]
  avail=lambda i:[c for c in range(k) if all(states[j]!=c for j in bits(a[i]))]
  u=min(U,key=lambda i:len(avail(i)));sub=[]
  for c in avail(u):
   states[u]=c;sub.append(trace());states[u]=-1
  return [u,sub]
 return dict(pairs=[pts[u] for u in ids],seed=start,trace=trace())
D=json.loads((p/'cutwidth.json').read_text())
traces={t:cert(int(t),d) for t,d in D.items() if not d['clique']}
(p/'cut-traces.json').write_text(json.dumps(traces,separators=(',',':')))
print('trace counts',len(traces),[(d['width'],sum(len(u['pairs']) for t,u in traces.items() if D[t]['width']==d['width'])) for d in [dict(width=3),dict(width=4)]])

from cover import *
def pack(dom):
 a=[x for x in range(4096) if dom>>x&1]
 reps={labels[x]:x for x in a}
 masks=sorted(reps,key=int.bit_count)
 best=[]
 for k in masks:
  if not any(b&k==b for b in best):best.append(k)
 @lru_cache(None)
 def solve(items):
  if not items:return ()
  b=items[0]
  take=(b,)+solve(tuple(k for k in items[1:] if k&b==0))
  if b.bit_count()==1:return take
  skip=solve(items[1:]);return take if len(take)>=len(skip) else skip
 return [reps[b] for b in solve(tuple(best))]
if __name__=='__main__':
 roots=json.loads((Path(__file__).resolve().parent/'roots.json').read_text());data={}
 for k,(n,l,h,a,b) in roots.items():
  m=int(k);lists=[pack(univ^par[m]),pack(par[m])]
  data[k]=lists
  for p,li in enumerate(lists):
   assert all((x&m).bit_count()%2==p for x in li) and all(labels[x]&labels[y]==0 for x,y in combinations(li,2))
 hist=Counter();gap=Counter()
 for k,li in data.items():
  v=roots[k];hist[sum(map(len,li))]+=v[0];gap[sum(v[-2:])-sum(map(len,li))]+=v[0]
 print('packing histogram',sorted(hist.items()),'cover gap',sorted(gap.items()))
 (Path(__file__).resolve().parent/'packs.json').write_text(json.dumps(data))

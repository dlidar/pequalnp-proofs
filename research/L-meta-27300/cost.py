import itertools
def target(x):
    a,b,c,d=[(x>>i)&1 for i in range(4)]
    return (a and c) or (b and d) or (b and c)
def dp(rows):
    k=len(rows);top=(1<<k)-1
    raw=[sum(1<<i for i,x in enumerate(rows) if x>>j&1) for j in range(4)]
    opt={0:0,top:0};layers=[set(opt),set(raw)|{top^v for v in raw}]
    for v in layers[1]:opt.setdefault(v,1)
    for m in range(2,5):
        cur=set()
        for i in range(1,m):
            for a,b in itertools.product(layers[i],layers[m-i]):
                cur.update([a|b,a&b])
        cur.update([top^v for v in cur]);cur-=opt.keys();layers.append(cur)
        for v in cur:opt[v]=m
    return [opt.get(i,5) for i in range(top+1)],raw,sum(1<<i for i,x in enumerate(rows) if target(x))
pos=[x for x in range(16) if target(x) and all(not target(x^1<<i) for i in range(4) if x>>i&1)]
neg=[x for x in range(16) if not target(x) and all(target(x|1<<i) for i in range(4) if not x>>i&1)]
for k in range(5):
    for extras in itertools.combinations([x for x in range(16) if x not in pos+neg],k):
        rows=pos+neg+list(extras);cost,raw,target_sig=dp(rows)
        if cost[target_sig]==5:
            print(rows,raw,target_sig,len(cost),flush=True)
            import json
            from pathlib import Path
            Path(__file__).with_name('cost.json').write_text(json.dumps([rows,cost,raw,target_sig]))
            quit()

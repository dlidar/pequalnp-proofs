from pathlib import Path
import json
import upper
p=Path(__file__).resolve().parent;orig=set(upper.edges);best=None
for delta,errors in json.loads((p/'nearest.json').read_text()):
 if len(errors)!=1:continue
 upper.edges=sorted(orig^{tuple(e) for e in delta});upper.aset=set(upper.edges)
 out=upper.witnesses()
 print(delta,errors,len(out['gates']),flush=True)
 if len(out['gates'])<=14 and (best is None or len(out['gates'])<len(best['gates'])):
  best=dict(delta=delta,errors=errors,gates=out['gates'])
  (p/'single-error.json').write_text(json.dumps(best))

import json
from pathlib import Path
from upper import target
p=Path(__file__).resolve().parent
for i in range(8):
 w=[x|((1-(x>>i&1))<<8) for x in range(256)]
 pos=[x for x in range(256) if target(x) and not any(target(y) and y!=x and w[x]&w[y]==w[y] for y in range(256))]
 neg=[x for x in range(256) if not target(x) and not any(not target(y) and y!=x and w[x]&w[y]==w[x] for y in range(256))]
 labs=[sum((w[x]>>j&1)<<k for k,x in enumerate(pos+neg)) for j in range(9)]
 (p/f'raw{i}.task').write_text(f'{len(pos)} {len(neg)} 9\n'+' '.join(map(str,labs))+'\n')

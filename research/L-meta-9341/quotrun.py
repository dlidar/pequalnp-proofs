import subprocess,json
from rects import *
for s,budgets in [(3,[14]),(7,[13,14,15])]:
 cells,opts=quotient(s); opts=list(opts.items())
 inp=''.join(f'{i} {len(o)} {m&((1<<64)-1)} {m>>64}\n' for i,(m,o) in enumerate(opts))
 for b in budgets:
  f=d/f'q{s}-{b}.log'
  r=subprocess.run([str(d/'orbit_search'),str(len(cells)),str(b),str(21//s)],input=inp,timeout=1140,text=True,capture_output=True,check=True)
  f.write_text(r.stdout)
  print(s,b,r.stdout.strip(),flush=True)
  if r.stdout.startswith('COVER'):
   rect=[z for t in r.stdout.split()[1:] for z in opts[int(t)][1]]
   assert len(rect)<=b and validate(rect)==0
   (d/f'sym{s}-{b}.json').write_text(json.dumps(rect))
   if len(rect)<=13:(d/'sym-witness.json').write_text(json.dumps(rect))
   break

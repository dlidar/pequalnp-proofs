from affine import *
import subprocess
cells,opts=quotient(7); opts=list(opts.items())
inp=''.join(f'{i} {len(o)} {m&((1<<64)-1)} {m>>64}\n' for i,(m,o) in enumerate(opts))
todo=set(cells)
for p in cells:
 if p not in todo:continue
 orbitset={(r[p[0]]%7,(c[p[1]]-(r[p[0]]-r[p[0]]%7))%21) for _,r,c in actions()}
 assert orbitset<=set(cells);todo-=orbitset
 i=cells.index(p);r=subprocess.run([str(d/'orbit_search'),'112','13','3',str(i)],input=inp,text=True,capture_output=True,check=True)
 print(i,len(orbitset),r.stdout.strip(),flush=True)
 if r.stdout.startswith('COVER'):
  rect=[z for t in r.stdout.split()[1:] for z in opts[int(t)][1]]
  assert len(rect)<=13 and validate(rect)==3
  (d/'three-missed.json').write_text(json.dumps(rect));break

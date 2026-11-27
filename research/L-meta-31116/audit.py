from pathlib import Path
import re
mods=['Reference','Universal','Boundary','Merge','Features','Alternation','Late']
out=['import '+m for m in mods]
for m in mods:
 ns=''
 for ln in Path(m+'.lean').read_text().splitlines():
  if ln.startswith('namespace '):ns=ln.split()[1]
  mo=re.search(r'(?:^|\] )theorem (\w+)',ln)
  if mo:out.append('#print axioms '+ns+'.'+mo[1])
Path('Audit.lean').write_text('\n'.join(out)+'\n')

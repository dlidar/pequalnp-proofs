from pathlib import Path
import re,sys
mods=sys.argv[1:];assert mods
stack=[];names=[]
for m in mods:
    stack.clear()
    for l in Path(m+'.lean').read_text().splitlines():
        if l.startswith('namespace '):stack.append(l.split()[1])
        if l.startswith('end ') and stack:stack.pop()
        r=re.match(r'theorem ([\w.]+)',l)
        if r:names.append('.'.join(stack+[r[1]]))
assert len(set(names))==len(names)
Path('Audit.lean').write_text(''.join('import '+m+'\n' for m in mods)+''.join('#print axioms '+n+'\n' for n in names))

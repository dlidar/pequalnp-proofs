"""Check the axiom report of every named theorem in the given compiled modules."""
from pathlib import Path
import re, subprocess,sys
root=Path(__file__).resolve().parent
modules=sys.argv[1:]
names=[]
for module in modules:
 source=(root/(module+'.lean')).read_text()
 namespace=re.search(r'^namespace (\S+)',source,re.M).group(1)
 names += [namespace+'.'+name for name in re.findall(r'^(?:theorem|lemma) (\S+)',source,re.M)]
audit=root/'Audit.lean'
audit.write_text(''.join('import '+m+'\n' for m in modules)+'\n'+''.join('#print axioms '+n+'\n' for n in names))
r=subprocess.run(['bash',str(root/'build.sh'),'Audit'],capture_output=True,text=True)
(root/'audit.log').write_text(r.stdout+r.stderr)
assert r.returncode==0, 'build failed'
for n in names:
 m=re.search("'"+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r.stdout)
 assert m and set((m[1] or '').split(', '))<={'','propext','Classical.choice','Quot.sound'}, n
print('verified',len(names),'theorems across',*modules)

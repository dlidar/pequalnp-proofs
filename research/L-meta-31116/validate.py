from pathlib import Path
import re
text=Path('audit-final.log').read_text()
count=Path('Audit.lean').read_text().count('#print axioms')
found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
assert len(found)==count and len({x for x,_ in found})==count
assert all(set(a.split(', '))<={'','propext','Quot.sound','Classical.choice'} for _,a in found)
Path('verified').write_text(str(count)+'\n');print(count,'audited theorems')

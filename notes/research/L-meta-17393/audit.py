"""Produce or verify the full axiom audit for the research modules."""
from pathlib import Path
import re
import sys
modules = (Path(__file__).parent/'modules.txt').read_text().split()
root = Path(__file__).parent
names = []
for mod in modules:
    ns = ''
    for line in (root/(mod+'.lean')).read_text().splitlines():
        if line.startswith('namespace '):
            ns = line.split()[1]
        m = re.match(r'(?:theorem|lemma) (\w+)',line)
        if m:
            names.append(ns+'.'+m[1])
if len(sys.argv)==1:
    print('\n'.join('import '+m for m in modules))
    print('\n'.join('#print axioms '+x for x in names))
else:
    raw = Path(sys.argv[1]).read_text()
    allowed = {'propext','Classical.choice','Quot.sound'}
    assert 'error:' not in raw
    for name in names:
        if f"'{name}' does not depend on any axioms" in raw:
            continue
        m = re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",raw)
        assert m and set(x.strip() for x in m[1].split(',')) <= allowed, name
    print(f'{len(names)} public theorems passed the allowed-axiom audit')

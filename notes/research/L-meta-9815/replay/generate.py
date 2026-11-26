"""Expand integer witness matrices into individual pinned-Lean replay modules."""
from pathlib import Path
import json,gzip,re,sys
here=Path(__file__).resolve().parent
dest=Path(sys.argv[1])
data=json.loads(gzip.decompress((here/'certificates.json.gz').read_bytes()))
matrices=['#['+', '.join('#'+str(row) for row in matrix)+']' for matrix in data['matrices']]
for name,source in data['templates'].items():
    if not re.fullmatch(r'(Cert|Strong)[0-9]+\.lean',name):raise ValueError(name)
    (dest/name).write_text(re.sub(r'@matrix([0-9]+)@',lambda m:matrices[int(m[1])],source))

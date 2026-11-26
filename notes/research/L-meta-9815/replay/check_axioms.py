"""Check every named Lean result in the replay against the project axiom list."""
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
names = re.findall(r"^#print axioms (\S+)", Path(sys.argv[1]).read_text(), re.M)
output = Path(sys.argv[2]).read_text()
if not names:
    raise SystemExit("Empty declaration list")
for name in names:
    pattern = "'" + re.escape(name) + r"' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])"
    match = re.search(pattern, output)
    if match is None:
        raise SystemExit(f"Missing audit output for {name}")
    axioms = {x.strip() for x in (match[1] or "").split(",") if x.strip()}
    if axioms - allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
print(f"Verified axioms of {len(names)} declarations")

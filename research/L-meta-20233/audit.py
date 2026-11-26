"""Audit all named public theorems in the encoder classification and circuit witnesses."""
from pathlib import Path
import re,subprocess
d=Path(__file__).parent
names=['FactorCriterion','SplitCore',*['Cert'+str(i) for i in range(8)],'Classification','UpperCore',*['Pos'+str(i) for i in range(10)],'Full','Types','Isolation','ForcedOr','Match']
def declared(n):
 out=[];stack=[]
 for line in (d/(n+'.lean')).read_text().splitlines():
  if m:=re.match(r'^namespace (\S+)',line):stack.append(m[1])
  elif line.startswith('end ') and stack:stack.pop()
  elif m:=re.match(r'^theorem (\S+)',line):out.append('.'.join(stack+[m[1].rstrip(':')]))
 return out
def audit(mods,file):
 ts=[x for n in mods for x in declared(n)]
 src=d/(file+'.lean')
 src.write_text(''.join('import '+n+'\n' for n in mods)+''.join('#print axioms '+t+'\n' for t in ts))
 res=subprocess.run(['lean',src.name],cwd=d,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (d/(file+'.log')).write_text(res.stdout)
 assert res.returncode==0
 for t in ts:
  m=re.search("'"+re.escape(t)+r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",res.stdout)
  assert m and (not m[1] or set(re.findall(r'[\w.]+',m[1]))<={'propext','Classical.choice','Quot.sound'}),t
 return len(ts)
r=audit(names,'ProofAudit')
for n in ['Upper','Near','Quotient24','EditNear']:r+=audit([n],n+'Audit')
print(r,'public theorems passed')

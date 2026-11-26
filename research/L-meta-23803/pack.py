from pathlib import Path
import re
p=Path(__file__).resolve().parent/'split'
order=(p/'order').read_text().splitlines()[:-1]
chunks=[];to={};cur=[];score=0
for name in order:
 src=(p/(name+'.lean')).read_text()
 bulk=65000 if name.startswith('Branch') or len(re.findall('import ',src))>2 else 12000
 if cur and score+bulk>125000:chunks.append(cur);cur=[];score=0
 to[name]='Pack'+str(len(chunks));cur.append(name);score+=bulk
if cur:chunks.append(cur)
for i,names in enumerate(chunks):
 deps=set();body=[]
 for n in names:
  src=(p/(n+'.lean')).read_text()
  for mod in re.findall(r'^import (\w+)$',src,re.M):
   d=to.get(mod,mod)
   if d!='Pack'+str(i):deps.add(d)
  body.append(re.sub(r'^import \w+\n','',src,flags=re.M))
 (p/f'Pack{i}.lean').write_text(''.join('import '+dep+'\n' for dep in sorted(deps))+''.join(body))
final=p/'Lower.lean';src=final.read_text();new=re.sub(r'^import Branch\d+\n','',src,flags=re.M)
(p/'Final.lean').write_text(''.join('import '+dep+'\n' for dep in sorted({to['Branch'+str(i)] for i in range(48)}))+new)
(p/'packed-order').write_text('\n'.join(['Pack'+str(i) for i in range(len(chunks))]+['Final'])+'\n')
print('packed count',len(chunks))

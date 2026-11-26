from math import gcd,lcm
from rects import *
def actions():
 for a in range(1,21):
  if gcd(a,21)>1:continue
  for b in range(21):
   r=[(a*i+b)%21 for i in range(21)]
   for c0 in range(21):
    c=[(a*j+c0)%21 for j in range(21)]
    if all({c[j] for j in range(21) if rows[i]>>j&1}=={j for j in range(21) if rows[r[i]]>>j&1} for i in range(21)):
     yield (a,b,c0),r,c
def cycles(p):
 unseen=set(range(len(p)));cy=[]
 while unseen:
  i=min(unseen);t=[]
  while i in unseen:t.append(i);unseen.remove(i);i=p[i]
  cy.append(t)
 return cy
if __name__=='__main__':
 from collections import Counter
 reps={}
 for act,r,c in actions():
  rc,cc=cycles(r),cycles(c); profile=(act[0],tuple(sorted(map(len,rc))),tuple(sorted(map(len,cc))))
  reps.setdefault(profile,(act,r,c))
 for (_,rs,cs),(act,r,c) in reps.items():
  order=lcm(*rs,*cs)
  if order in (2,3,6,7):print(act,'order',order,'fixed',rs.count(1),cs.count(1))
 (d/'sym-actions.json').write_text(json.dumps([[*act,r,c] for _,(act,r,c) in reps.items()]))

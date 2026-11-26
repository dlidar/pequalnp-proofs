from itertools import combinations
from collections import Counter
D={0,1,3,9}
F=[(i,j) for i in range(13) for j in range(13) if (i-j)%13 in D]
N=[]
for Q in combinations(range(13),4):
 hits=[sum((i-j)%13 in D for i in Q) for j in range(13)]
 if max(hits)<=2:N.append(sum(1<<i for i in Q)+sum(1<<(13+j) for j,h in enumerate(hits) if h==0))
def calc(a):
 def lift(x):return x|((1<<26) if any(x>>k&1 for k in a) else 0)
 pos=[lift((1<<i)|(1<<(13+j))) for i,j in F];neg=list(map(lift,N))
 bad=[(i,j) for i,j in combinations(range(52),2) if all((pos[i]&pos[j])&~x for x in neg)]
 print(a,len(bad),[(F[i],F[j]) for i,j in bad])
 return pos,neg,bad
ads=[[],[0],[13],[0,1],[13,14],[0,13],[0,14]]
if __name__=='__main__':
 for a in ads:calc(a)

"""Recompute the optimum on each recorded halfspace using assignment sets.

Each subproblem is a bitset of whole assignments. A test with only one
nonempty child gives no information. A nonempty region is terminal exactly
when some axiom is false throughout it.
"""
from functools import lru_cache
from pathlib import Path
from cover import bad, par, raw, univ
def leaves(region):
 @lru_cache(None)
 def cost(s):
  if not s:return 0
  if any(s & ~violations==0 for violations in bad):return 1
  best=4097
  for bit in raw:
   left=s&bit
   right=s^left
   if left and right:best=min(best,cost(left)+cost(right))
  assert best<=4096
  return best
 try:return cost(region)
 finally:cost.cache_clear()
if __name__=='__main__':
 import sys
 for line in (Path(__file__).parent/'trees.txt').read_text().splitlines():
  m,a,b=map(int,line.split())
  if sys.argv[1:] and m not in set(map(int,sys.argv[1:])):continue
  assert leaves(univ ^ par[m])==a and leaves(par[m])==b
  print(m,a,b,flush=True)

from itertools import combinations
from pathlib import Path
from cone import write
d=Path('two-input-gates')
d.mkdir(exist_ok=True)
for a,b in combinations(range(8),2):
 for c in set(range(8))-{a,b}:
  for first in 'ao':
   for second in 'ao':write(d/f'{a}{b}{first}{c}{second}.task',[(first,a,b),(second,8,c)])

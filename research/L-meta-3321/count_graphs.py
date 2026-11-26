"""Count labeled square-free incidence graphs on up to four points and four lines by checked cases."""
from collections import Counter

def count(n):
    result=Counter()
    for table in range(1<<(n*n)):
        rows=[(table>>(i*n)) & ((1<<n)-1) for i in range(n)]
        if any((x&y).bit_count()>1 for i,x in enumerate(rows) for y in rows[:i]): continue
        nb=[set() for _ in range(2*n)]
        for i,row in enumerate(rows):
            for j in range(n):
                if row & (1<<j):
                    nb[i].add(n+j);nb[n+j].add(i)
        todo={v for v,s in enumerate(nb) if s}
        components=[]
        while todo:
            seen=set();stack=[todo.pop()]
            while stack:
                v=stack.pop();seen.add(v)
                others=todo & nb[v];todo-=others;stack.extend(others)
            components.append(seen)
        if all(sum(len(nb[v]) for v in part)//2 < len(part) for part in components): kind='forest'
        elif len(components)==1 and all(len(nb[v])==2 for v in components[0]):kind='cycle and isolates'
        else:kind='outside these cases'
        result[kind]+=1
    return result
if __name__=='__main__':
    for n in range(5):print(n,count(n))

from circuit import compile_circuit
g,(num,rank,valid,pick)=compile_circuit(1)
print(len(g.program))
for op,a,b in g.program:print({'and':0,'or':1,'not':2}[op],a,b or 0)
print(*num,*rank,valid,*(i for pair in pick for i in pair))

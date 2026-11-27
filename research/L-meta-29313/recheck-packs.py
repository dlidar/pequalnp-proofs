"""Replay lower bounds for decoders receiving one free complemented input or gate."""
from labels import cases, graph, json, p
from collections import Counter
import subprocess

def replay():
    packs=json.loads((p/'decoder-packs.json').read_text())
    pins=json.loads((p/'pinning.json').read_text())
    inputs=[]
    bounds=[]
    for _,op,i,j,h in cases:
        row=packs[hex(h)]
        pos,neg=row['P'],row['N']
        assert all(0<=x<256 and graph(x) for x in pos)
        assert all(0<=x<256 and not graph(x) for x in neg)
        samples=[x+256*(1-((h>>x)&1)) for x in pos+neg]
        inputs.append(' '.join(map(str,[len(pos),len(neg)]+samples)))
        bounds.append((row['bound'], pins[hex(h)]['exact_lower']))
    result=subprocess.run([p/'smalldec'],input='\n'.join(inputs)+'\n',text=True,capture_output=True,check=True)
    assert [int(x) for x in result.stdout.split()]==[x for x,y in bounds]
    print(Counter(max(14,x,y) for x,y in bounds))
if __name__=='__main__':replay()

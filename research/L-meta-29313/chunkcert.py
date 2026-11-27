"""Split large powerset checks into disjoint subcubes without changing the matrix."""
from pathlib import Path
import json,itertools
p=Path(__file__).resolve().parent
w=json.loads((p/'weights-29313.json').read_text())
raw=sum(((x>>3)&1)<<x for x in range(256))
data=w[hex(raw)]
pre='import Cert3Base\nopen Finset\nnamespace Graph29313.Cert3\n'
end='end Graph29313.Cert3\n'
(p/'SplitRows.lean').write_text(pre+"""
theorem split_rows {α : Type} [DecidableEq α] {U : Finset α} {Q : Finset α → Prop} (j : α)
    (off : ∀ s ∈ (U.erase j).powerset, Q s)
    (on : ∀ s ∈ (U.erase j).powerset, Q (insert j s)) :
    ∀ s ∈ U.powerset, Q s := by
  intro s hs
  have sub := mem_powerset.mp hs
  by_cases hj : j∈s
  · have h : s.erase j ⊆ U.erase j := by
      intro k hk
      exact mem_erase.mpr ⟨(mem_erase.mp hk).1,sub (mem_erase.mp hk).2⟩
    simpa only [insert_erase hj] using on (s.erase j) (mem_powerset.mpr h)
  · apply off s (mem_powerset.mpr ?_)
    intro k hk
    exact mem_erase.mpr ⟨fun he => hj (he ▸ hk), sub hk⟩
"""+end)
order=['SplitRows']
for j in [6,7]:
    bits=[k for k,x in enumerate(data['N']) if not (x>>j)&1][:3]
    imports=[];proof=[]
    for num,opts in enumerate(itertools.product([0,1], repeat=3)):
        U=f'(univ.filter (fun k => enc (bits (N k)) 3 ({j} : Fin 9)=false))'
        expr='s'
        for k in bits:U=f'({U}.erase {k})'
        for k,flag in reversed(list(zip(bits,opts))):
            if flag:expr=f'(insert {k} {expr})'
        prop=f'∀ s∈{U}.powerset, (∑ k∈univ.filter (fun k => enc (bits (P k)) 3 ({j} : Fin 9)=true), max 0 (∑ z∈{expr}, w k z)) ≤ cap'
        mod=f'Row{j}Chunk{num}'
        (p/(mod+'.lean')).write_text(pre+'set_option maxRecDepth 16000\nset_option maxHeartbeats 4000000\ntheorem chunk'+str(j)+'_'+str(num)+' : '+prop+' := by decide +kernel\n'+end)
        order.append(mod);imports.append('import '+mod)
        proof.append(f'  · exact chunk{j}_{num}')
    def tree(k,U,opts):
        if k==3:return f'chunk{j}_'+str(sum(v<<(2-z) for z,v in enumerate(opts)))
        expr='s'
        for n,flag in reversed(list(zip(bits,opts))):
            if flag:expr=f'(insert {n} {expr})'
        pred=f'(fun s : Finset (Fin 10) => (∑ k∈univ.filter (fun k => enc (bits (P k)) 3 ({j} : Fin 9)=true), max 0 (∑ z∈{expr}, w k z)) ≤ cap)'
        nxt=f'({U}.erase {bits[k]})'
        return f'(split_rows (U := {U}) (Q := {pred}) {bits[k]} '+tree(k+1,nxt,opts+[0])+' '+tree(k+1,nxt,opts+[1])+')'
    U=f'(univ.filter (fun k => enc (bits (N k)) 3 ({j} : Fin 9)=false))'
    src='\n'.join(imports)+'\nimport SplitRows\n'+pre.removeprefix('import Cert3Base\n')+f'theorem test{j} : tests {j} :=\n  '+tree(0,U,[])+'\n'+end
    (p/f'Cert3Test{j}.lean').write_text(src)
    order.append(f'Cert3Test{j}')
(p/'chunk-order').write_text('\n'.join(order)+'\n')

"""Generate the eight raw-negation certificates from exact integer matrices."""
from pathlib import Path
import json
p=Path(__file__).resolve().parent
weights=json.loads((p/'weights-29313.json').read_text())
def vec(row):return '!['+','.join(map(str,row))+']'
for i in range(8):
    raw=sum(((x>>i)&1)<<x for x in range(256))
    w=weights[hex(raw)];P=w['P'];N=w['N'];r=len(P);c=len(N)
    source=f'''import Signed
open Finset PEqualNP.Research.TripleFormulaMass
namespace Graph29313.Cert{i}
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
def P : Fin {r} → Nat := {vec(P)}
def N : Fin {c} → Nat := {vec(N)}
def w : Fin {r} → Fin {c} → Int := {vec([vec(row) for row in w['weights']])}
def cap : Int := {w['cap']}
def tests (i : Fin 9) : Prop := ∀ s∈(univ.filter (fun j => enc (bits (N j)) {i} i=false)).powerset,
    (∑ j∈univ.filter (fun j => enc (bits (P j)) {i} i=true),max 0 (∑ k∈s,w j k)) ≤ cap
instance (i : Fin 9) : Decidable (tests i) := by unfold tests; infer_instance
'''
    for j in range(9):source+=f'theorem test{j} : tests {j} := by decide +kernel\n'
    source+=f'''theorem bound (f : Formula (Fin 9)) (ok : ∀ x,f.eval (enc x {i})=target x) : 13 < f.leaves := by
  apply signed_lower P N w {i} cap 13 (by decide +kernel) (by decide +kernel) _ (by decide) (by decide +kernel) f ok
  intro j
  fin_cases j <;> first | exact test0 | exact test1 | exact test2 | exact test3 | exact test4 | exact test5 | exact test6 | exact test7 | exact test8
end Graph29313.Cert{i}
'''
    (p/f'Cert{i}.lean').write_text(source)

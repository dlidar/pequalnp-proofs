"""Generate Lean width theorems for every four-versus-four split."""
from cutwidth import *
D=json.loads((p/'cutwidth.json').read_text());T=json.loads((p/'cut-traces.json').read_text())
def vec(s):return '!['+','.join(map(str,s))+']'
for t in range(256):
 if t.bit_count()!=4:continue
 X=masks(t);Y=masks(t^255);ax=[i for i in range(8) if t>>i&1];by=[i for i in range(8) if not t>>i&1]
 perm=[ax.index(i) if i in ax else 4+by.index(i) for i in range(8)]
 row=[sum(int(fun(x|y))<<j for j,y in enumerate(Y)) for x in X];d=D[str(t)]
 k=d['width'];code=[sum(int(any(a&x==a for a in gen))<<j for j,gen in enumerate(d['uppers'])) for x in X]
 pairs=d['clique'] or T[str(t)]['pairs']
 ids=[(X.index(a),X.index(b)) for a,b in pairs];n=len(ids)
 s=f"""import Four
namespace Graph32249.Cut{t}
open MonotoneCut
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000
def order : Fin 8 → Nat := {vec(perm)}
def rows : Fin 16 → Nat := {vec(row)}
def codes : Fin 16 → Nat := {vec(code)}
def eval (a b : Four) := target (splitInput order a b)
theorem table_eq : eval = rowFunction rows := by
  funext a b
  exact (show ∀ x y : Four, eval x y = rowFunction rows x y by decide +kernel) a b
theorem upper : Can eval {k} := by
  rw [table_eq]
  exact from_checks (v:=codes) (by decide +kernel)
def pairs : Fin {n} → Four × Four := {vec([f'mkPair {a} {b}' for a,b in ids])}
theorem lower (enc : Can eval {k-1}) : False := by
  rw [table_eq] at enc
  obtain ⟨e,he⟩ := enc
  have bad : ∀ v, Violates (rowFunction rows) (pairs v) := by
    intro v
    fin_cases v
"""
 for num,(a,b) in enumerate(ids):
  y=next(j for j in range(16) if row[a]>>j&1 and not row[b]>>j&1)
  s+=f'    · exact ⟨⟨{y}⟩,by decide +kernel⟩\n'
 s+='  obtain ⟨col,hcol⟩ := color_of_code he pairs bad\n'
 for i,(a,b) in enumerate(ids):
  for j,(c,v) in enumerate(ids[:i]):
   if a&v==a or c&b==c:
    side='inl' if a&v==a else 'inr'
    s+=f'  have e{i}_{j} : (col {i}).val ≠ (col {j}).val := fun h => hcol {i} {j} (Or.{side} (by decide +kernel)) (Fin.ext h)\n'
 s+=f'  omega\ntheorem exact_width (j : Nat) : Can eval j ↔ {k}≤j := by\n  constructor\n  · intro h;by_contra! small;exact lower (smaller h (by omega))\n  · exact smaller upper\nend Graph32249.Cut{t}\n'
 (p/f'Cut{t}.lean').write_text(s)

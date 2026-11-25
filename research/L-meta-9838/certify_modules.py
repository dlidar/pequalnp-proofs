import hashlib,json
from search_modules import W,SOURCE,representatives,build_stars,target_word,samples,synth,running
from check_rup import verify
expected = json.loads((SOURCE/'module-certificates.json').read_text())
cases = {(tuple(case['centers']), tuple(case['profiles'])): case for case in expected}
reports=[]
for side,c,b in representatives():
    k=len(c);ms=sorted(b);key=str(k)+'_'+'.'.join(map(str,ms))
    if (tuple(c),tuple(ms)) not in cases: continue
    if not running(): break
    limit=len(build_stars(k,ms)[0])-1; table=target_word(k,ms); inputs=k+len(ms);tests=samples(k,ms,table)
    pr=W/('proof_'+key.replace('.','-')+'.lrat');cnf=pr.with_suffix('.cnf')
    st,_=synth(inputs,limit,tests,table,90,free=True,certificate=pr)
    if st=='UNSAT':
        additions=verify(cnf,pr)
        reports.append(dict(centers=c,profiles=ms,inputs=inputs,gates=limit,sample_count=len(tests),additions=additions,cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),proof_sha256=hashlib.sha256(pr.read_bytes()).hexdigest()))
        assert reports[-1]['cnf_sha256'] == cases[(tuple(c),tuple(ms))]['cnf_sha256']
        (W/'module-certificates.json').write_text(json.dumps(reports,indent=2))
        print(key,additions,flush=True)
    else:print(key,st,flush=True)

if len(reports) != len(cases):
    raise SystemExit('Some certificates did not finish.')

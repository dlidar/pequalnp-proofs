from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'Cert3.lean').read_text();base,rest=s.split('theorem test0',1);tests,body=('theorem test0'+rest).split('theorem bound',1)
(p/'Cert3Base.lean').write_text(base+'end Graph29313.Cert3\n')
for i,line in enumerate(tests.strip().splitlines()):
    assert line.startswith('theorem test'+str(i)+' ')
    (p/f'Cert3Test{i}.lean').write_text('import Cert3Base\nnamespace Graph29313.Cert3\nset_option maxRecDepth 16000\nset_option maxHeartbeats 4000000\n'+line+'\nend Graph29313.Cert3\n')
(p/'Cert3.lean').write_text(''.join('import Cert3Test'+str(i)+'\n' for i in range(9))+'open Finset PEqualNP.Research.TripleFormulaMass\nnamespace Graph29313.Cert3\nset_option maxRecDepth 16000\nset_option maxHeartbeats 4000000\ntheorem bound'+body)

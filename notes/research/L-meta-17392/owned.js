// Enumerate every triangle-term subset and the edge that can be factored out of each group.
// Runnable with Node.js. Bit i is the ith edge input of the posted theorem.
const terms = [[0,1,4],[0,2,5],[0,3,6],[1,2,7],[1,3,8],[2,3,9],[4,5,7],[4,6,8],[5,6,9],[7,8,9]];
const masks = terms.map(t => t.reduce((bits,i) => bits | (1<<i),0));
function pop(n) {
  let k=0;
  for (; n; n&=n-1) k++;
  return k;
}
function assert(ok) { if (!ok) throw Error("cross-check failed"); }
function enumerate() {
  const hist = Array(1024).fill(0);
  for(let row=0;row<1024;row++) {
    const key=masks.reduce((v,t,j)=>v|((row&t)===t?1<<j:0),0);
    hist[key]++;
  }
  const costs=Array(1024).fill(11);
  const covers=Array(1024).fill(0);
  for(let c=0;c<1024;c++) {
    const owned=masks.reduce((v,t,j)=>v|(c&t?1<<j:0),0);
    for(let s=owned;;s=(s-1)&owned) {
      if(pop(c)<costs[s]) { costs[s]=pop(c);covers[s]=c; }
      if(!s)break;
    }
  }
  const eligible=[];
  for(let s=1;s<1024;s++) {
    const t=pop(s), g=costs[s];
    // t inner ANDs, g outer ANDs, t-1 ORs and two available NOT slots.
    if(t+g>11 || 2*t+g-1+2>22)continue;
    const misses=hist.reduce((v,n,k)=>v+(k && !(s&k)?n:0),0);
    eligible.push({s,g,t,misses});
  }
  const best=Math.min(...eligible.map(x=>x.misses));
  const winners=eligible.filter(x=>x.misses===best);
  const chosen=winners[0];
  const termsByOwner=new Map();
  for(let j=0;j<10;j++)if(chosen.s>>j&1) {
    const t=terms[j],o=t.find(i=>covers[chosen.s]>>i&1);
    if(!termsByOwner.has(o))termsByOwner.set(o,[]);
    termsByOwner.get(o).push(t.filter(i=>i!==o));
  }
  const gates=[];
  function put(op,i,j){gates.push([op,i,j]);return 9+gates.length;}
  function join(xs){return xs.reduce((a,b)=>put('or',a,b));}
  let pads=22-(2*chosen.t+chosen.g-1);
  put('not',0,null);put('not',10,null);
  for(let k=2;k<pads;k++)put('or',0,0);
  const stars=[];
  for(const [o,ws] of termsByOwner)stars.push(put('and',o,join(ws.map(([a,b])=>put('and',a,b)))));
  const output=join(stars);
  let fp=0,fn=0;
  for(let r=0;r<1024;r++) {
    const w=Array.from({length:10},(_,i)=>!!(r>>i&1));
    for(const [op,i,j] of gates)w.push(op==='not'?!w[i]:op==='and'?w[i]&&w[j]:w[i]||w[j]);
    const exact=terms.some(t=>t.every(i=>r>>i&1));
    if(w[output]&&!exact)fp++;
    if(!w[output]&&exact)fn++;
  }
  assert(gates.length===22 && fp===0 && fn===best && best===64 && winners.length===30 && eligible.length===997);
  assert(gates.filter(g=>g[0]==='not').length===2 && gates.filter(g=>g[0]==='and').length===11);
  return {allowed_nonempty_families:eligible.length,minimum_false_negatives:best,winners:winners.length,
    retained:chosen.s,owner_mask:covers[chosen.s],gates,output,false_positives:fp,false_negatives:fn};
}

console.log(JSON.stringify(enumerate(),null,2));

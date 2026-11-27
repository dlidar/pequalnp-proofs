// Exact formula costs for every maximal pair of opposite incomparable label sets in the five-cube.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;using U=uint32_t;
struct Witness {int cost;char op;U a,b;};
int main(){
  const U full=~U(0);unordered_map<U,Witness> vals;vector<vector<U>> lev(64);
  vals[0]={0,'0',0,0};vals[full]={0,'1',0,0};
  for(int i=0;i<5;i++){U t=0;for(int x=0;x<32;x++)if(x>>i&1)t|=U(1)<<x;vals[t]={1,'v',U(i),0};lev[1].push_back(t);}
  for(int k=2;k<64 && vals.size()<7581;k++){
    for(int j=1;j<=k/2;j++)for(U a:lev[j])for(U b:lev[k-j])for(char op:{'&','|'}) {
      U t=op=='&'?a&b:a|b;
      if(vals.emplace(t,Witness{k,op,a,b}).second)lev[k].push_back(t);
    }
  }
  assert(vals.size()==7581); // Independently check closure, costs and witness for every monotone truth function.
  for(auto [t,w]:vals){
    if(w.cost>1)assert(t==(w.op=='&'?(w.a&w.b):(w.a|w.b))&&w.cost==vals.at(w.a).cost+vals.at(w.b).cost);
    for(auto [v,q]:vals)if(q.cost&&w.cost){
      assert(vals.at(t&v).cost<=q.cost+w.cost && vals.at(t|v).cost<=q.cost+w.cost);
    }
  }
  array<U,32> inc{};for(U x=0;x<32;x++)for(U y=0;y<32;y++)if((x&y)!=x&&(x&y)!=y)inc[x]|=U(1)<<y;
  auto opposite=[&](U z){U o=full;while(z){o&=inc[__builtin_ctz(z)];z&=z-1;}return o;};
  unordered_set<U> closed{full};for(U col:inc){vector<U> extra;for(U m:closed)extra.push_back(m&col);closed.insert(extra.begin(),extra.end());}
  map<int,int> hist;map<int,pair<U,U>> examples;
  vector<pair<U,int>> sorted;for(auto [t,w]:vals)sorted.emplace_back(t,w.cost);
  sort(sorted.begin(),sorted.end(),[](auto a,auto b){return a.second<b.second||(a.second==b.second&&a.first<b.first);});
  for(U o:closed){
    U z=opposite(o);assert(opposite(z)==o);int k=-1;
    for(auto [t,c]:sorted)if(!(t&z)&&(o&t)==o){k=c;break;}
    assert(k>=0);hist[k]++;examples[k]={z,o};
  }
  cout<<"functions "<<vals.size()<<" maximal label pairs "<<closed.size()<<"\n";
  for(auto [k,n]:hist)cout<<k<<" leaves "<<n<<" pairs\n";
  auto [z,o]=examples.rbegin()->second;
  cout<<"worst zero mask "<<z<<" one mask "<<o<<"\n";
  for(U t:{z,o}){for(int x=0;x<32;x++)if(t>>x&1)cout<<x<<' ';cout<<"\n";}
}

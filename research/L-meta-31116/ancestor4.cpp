// Generate all distinct feature sets of live four-gate monotone inverter cones.
#include <cstdint>
#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using U=uint64_t;using Table=array<U,4>;
struct G{int a,b;bool join;};
vector<Table> sig;vector<G> prog;set<array<Table,4>> keys;
ofstream tasks("four.tasks"),programs("four.programs");
bool fn[256];
bool bit(Table const&t,int i){return (t[i/64]>>(i%64))&1;}
void save(){
 int live=8;
 for(int i=3;i>=0;i--)if(live>>i&1)for(int v:{prog[i].a,prog[i].b})if(v>=8)live|=1<<(v-8);
 if(live!=15)return;
 array<Table,4> key{sig[8],sig[9],sig[10],sig[11]};sort(key.begin(),key.begin()+3);if(!keys.insert(key).second)return;
 vector<int> p,n;
 for(int x=0;x<256;x++){
  bool h=bit(sig[11],x),extreme=true;
  for(int i=0;i<8;i++)if(((x>>i)&1)==int(fn[x])){
   int y=x^(1<<i);if(fn[y]==fn[x]&&bit(sig[11],y)==h)extreme=false;
  }
  if(extreme)(fn[x]?p:n).push_back(x);
 }
 assert(p.size()+n.size()<63);tasks<<keys.size()<<' '<<p.size()<<' '<<n.size()<<" 13";
 vector<int> rows=p;rows.insert(rows.end(),n.begin(),n.end());
 for(int j=0;j<13;j++){
  U v=0;for(unsigned l=0;l<rows.size();l++)if(bit(sig[min(j,11)],rows[l])!=(j==12))v|=U(1)<<l;
  tasks<<' '<<v;
 }
 tasks<<'\n';programs<<keys.size();for(auto g:prog)programs<<' '<<g.a<<' '<<g.b<<' '<<g.join;programs<<'\n';
}
void gen(){
 int n=sig.size();if(n==12){save();return;}
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(bool j:{false,true}){
  Table t;for(int l=0;l<4;l++)t[l]=j?(sig[a][l]|sig[b][l]):(sig[a][l]&sig[b][l]);
  if(find(sig.begin(),sig.end(),t)!=sig.end())continue;
  sig.push_back(t);prog.push_back({a,b,j});gen();prog.pop_back();sig.pop_back();
 }
}
int main(){
 for(int i=0;i<8;i++){Table t{};for(int x=0;x<256;x++)if(x>>i&1)t[x/64]|=U(1)<<(x%64);sig.push_back(t);}
 for(int x=0;x<256;x++)for(int e:{17,18,33,36,65,66,72,96,129,130,132,144,160,192})if((x&e)==e)fn[x]=true;
 gen();cout<<keys.size()<<" distinct four-ancestor feature sets\n";
}

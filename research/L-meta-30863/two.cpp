// All such replacements, retaining topological order and the final output wire.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Gate {int op,a,b;};
bool operator==(Gate x,Gate y){return x.op==y.op&&x.a==y.a&&x.b==y.b;}
using Row=array<uint64_t,4>;
using Gates=array<Gate,13>;
Row raw[21],goal{};
int edges[]={9,18,33,34,36,65,68,72,129,130,132,136,160,192};
int distance(const Gates&g,int from){
 for(int i=from;i<13;i++){
   auto [op,a,b]=g[i];for(int k=0;k<4;k++)raw[8+i][k]=op==0?(raw[a][k]&raw[b][k]):op==1?(raw[a][k]|raw[b][k]):~raw[a][k];
 }
 int d=0;for(int k=0;k<4;k++)d+=__builtin_popcountll(raw[20][k]^goal[k]);return d;
}
int main(){
 for(int x=0;x<256;x++){
   for(int i=0;i<8;i++)if(x>>i&1)raw[i][x/64]|=uint64_t(1)<<(x%64);
   for(int e:edges)if((x&e)==e){goal[x/64]|=uint64_t(1)<<(x%64);break;}
 }
 ifstream in("controls.txt");
 for(int seed=0;seed<2;seed++){
  Gates base;for(auto&g:base)in>>g.op>>g.a>>g.b;
  assert(distance(base,0)==1);array<vector<Gate>,13> alt;
  for(int i=0;i<13;i++)for(int a=0;a<8+i;a++){
   alt[i].push_back({2,a,a});
   for(int b=a;b<8+i;b++)for(int op=0;op<2;op++){Gate g{op,a,b};if(!(g==base[i]))alt[i].push_back(g);}
  }
  uint64_t count=0,one=0;Gates g=base;
  for(int i=0;i<13;i++)for(auto a:alt[i]){
   g=base;g[i]=a;
   auto check=[&](int start){
    int d=distance(g,start);count++;one+=(d==1);
    if(d==0){ofstream out("repair-witness.txt");for(auto h:g)out<<h.op<<" "<<h.a<<" "<<h.b<<"\n";exit(0);}
   };
   check(0);
   for(int j=i+1;j<13;j++){
    distance(g,i);
    for(auto b:alt[j]){if(a.op==2&&b.op==2)continue;g[j]=b;check(j);}
    g[j]=base[j];
   }
  }
  cout<<seed<<" "<<count<<" "<<one<<endl;
 }
}

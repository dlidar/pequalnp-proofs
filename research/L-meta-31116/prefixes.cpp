// Enumerate acyclic binary programs of at most four gates on the twenty boundary rows.
// A program with a repeated signal can bypass it and has a shorter representative.
#include <algorithm>
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
int raw_rows[]={17,18,33,36,65,66,72,96,129,130,132,144,160,192,15,28,42,56,84,136};
array<int,12> wire{};
array<unsigned char,1<<20> formula_cost;
array<int,1<<20> min_gates;
set<array<int,4>> worst_programs;
long long visits[5]={};
int price(int h){return formula_cost[((16383^(h&16383))<<6)|(h>>14)]-1;}
void walk(int used){
 int m=8+used;
 for(int a=0;a<m;a++)for(int b=a+1;b<m;b++){
  for(int h:{wire[a]&wire[b],wire[a]|wire[b]}){
   if(find(wire.begin(),wire.begin()+m,h)!=wire.begin()+m)continue;
   wire[m]=h;++visits[used+1];
   min_gates[h]=min(min_gates[h],used+1);
   if(used==3 && price(h)==14){
    array<int,4> p={wire[8],wire[9],wire[10],h};sort(p.begin(),p.begin()+3);worst_programs.insert(p);
   }
   if(used<3)walk(used+1);
  }
 }
}
int main(){
 ifstream f("mono.bin",ios::binary);assert(f.read((char*)formula_cost.data(),formula_cost.size()));
 min_gates.fill(100);
 for(int j=0;j<8;j++){
  for(int i=0;i<20;i++)wire[j]|=((raw_rows[i]>>j)&1)<<i;
  min_gates[wire[j]]=0;
 }
 min_gates[0]=min_gates[(1<<20)-1]=0;
 walk(0);
 ofstream programs("worst-programs.txt");
 for(auto p:worst_programs)programs<<p[0]<<' '<<p[1]<<' '<<p[2]<<' '<<p[3]<<'\n';
 for(int k=0;k<=4;k++){int count=0,mx=0;set<int> worst;
  for(int i=0;i<(1<<20);i++)if(min_gates[i]==k){count++;int d=price(i);if(d>mx){mx=d;worst.clear();}if(d==mx)worst.insert(i);}
  cout<<k<<" gates "<<count<<" traces, max "<<mx<<", "<<worst.size()<<" extremizers; "<<visits[k]<<" programs\n";
 }
 cout<<worst_programs.size()<<" extremal (predecessor set,output) pairs\n";
}

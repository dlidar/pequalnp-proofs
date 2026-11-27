// Direct enumeration without memoizing prefix states. Unlike catalog.py this
// retains repeated truth signals, unused gates and ordered gate histories.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
array<unsigned,12> w{};
vector<unsigned char> cost(1<<22,255);
int masks[]={9,18,33,34,36,65,68,72,129,130,132,136,160,192,7,14,21,28,56,66,112,144};
void visit(int d){
 for(int i=0;i<8+d;i++)for(int j=i;j<8+d;j++)for(unsigned v:{w[i]&w[j],w[i]|w[j]}){
   cost[v]=min((unsigned)cost[v],(unsigned)(d+1));
   if(d<3){w[8+d]=v;visit(d+1);}
 }
}
int main(){
 for(int i=0;i<8;i++){
   for(int r=0;r<22;r++)w[i]|=((masks[r]>>i)&1)<<r;
   cost[w[i]]=0;
 }
 visit(0);
 ifstream in("table.bin",ios::binary);vector<unsigned char> tab{istreambuf_iterator<char>(in),istreambuf_iterator<char>()};
 assert(tab.size()==1<<22);
 int hist[5][16]={};
 for(unsigned v=0;v<cost.size();v++)if(cost[v]<5){
  unsigned a=(~v)&16383,b=v>>14;
  int n=(a&&b)?tab[256*a+b]:0;assert(n<=15);
  hist[cost[v]][n]++;
 }
 assert(cost[3489792]==4&&hist[4][15]==1);
 for(auto&row:hist){for(int x:row)cout<<x<<' ';cout<<'\n';}
}

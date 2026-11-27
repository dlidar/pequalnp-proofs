// Enumerate complete product covers consistent with a 13-gate budget.
// At the first uncovered edge branch on its first selected covering product.
#include <array>
#include <algorithm>
#include <vector>
#include <iostream>
#include <cassert>
using namespace std;
struct Product{int a,b,e;};
vector<Product> products;vector<int> cover[14],sol;
int edges[]={9,18,33,34,36,65,68,72,129,130,132,136,160,192};
int req[256]={},ban[2048]={};long long visited=0,complete=0;
int bits(int x){return __builtin_popcount(x);}
void visit(int m,int sides){
 visited++;
 int k=sol.size();
 if(2*k-1+sides>13)return;
 if(m==16383){complete++;for(auto i:sol)cout<<products[i].a<<","<<products[i].b<<" ";cout<<"\n";return;}
 if(2*k+1+sides>13)return;
 int edge=-1,minOptions=10000;
 for(int j=0;j<14;j++)if(!(m>>j&1)){
   int cnt=0;for(int i:cover[j])if(!ban[i])cnt++;
   if(cnt<minOptions){minOptions=cnt;edge=j;}
 }
 vector<int> blocked;
 for(auto i:cover[edge])if(!ban[i]){
   auto p=products[i];int extra=(bits(p.a)>1&&!req[p.a])+(bits(p.b)>1&&!req[p.b]);
   req[p.a]++;req[p.b]++;sol.push_back(i);
   visit(m|p.e,sides+extra);
   sol.pop_back();req[p.a]--;req[p.b]--;ban[i]++;blocked.push_back(i);
 }
 for(int i:blocked)ban[i]--;
}
int main(int argc,char** argv){
 const bool partial=argc==2;
 for(int a=1;a<256;a++)for(int b=a+1;b<256;b++)if(!(a&b)){
   int e=0;for(int i=0;i<14;i++)if((edges[i]&a)&&(edges[i]&b))e|=1<<i;
   int bonus=0;if(partial)for(int v:{10,66,12})if((v&a)&&(v&b))bonus++;
   if(!e||bits(e)+bonus!=bits(a)*bits(b))continue;
   int id=products.size();products.push_back({a,b,e});assert(id<2048);
   for(int i=0;i<14;i++)if(e>>i&1)cover[i].push_back(id);
 }
 visit(0,0);cerr<<products.size()<<" products "<<visited<<" nodes "<<complete<<" surviving covers\n";
}

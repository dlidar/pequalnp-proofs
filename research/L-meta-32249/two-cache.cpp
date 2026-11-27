// Exclude short monotone circuits with two preliminary binary gates followed by a tree.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int R=16383,C=1023;vector<unsigned char> M(1<<24);
int rp[2],rn[2],ps[4],ns[4];unordered_map<uint32_t,bool> memo;
int cost(int a,int b){return a&&b?M[(a<<10)|b]:0;}
int fixboth(int a,int b){int v=0;for(int i=0;i<4;++i)v=max(v,cost(a&ps[i],b&ns[i]));return v;}
int lower(int a,int b){
 int q=cost(a,b);
 for(int i=0;i<2;++i)q=min(q,1+max(cost(a&~rp[i],b),cost(a,b&rn[i])));
 return min(q,2+fixboth(a,b));
}
bool fit(int a,int b,int d){
 if(cost(a,b)<=d)return true;
 for(int i=0;i<2;++i)if(!(a&~rp[i])&&!(b&rn[i]))return d>=1;
 if(d<2||lower(a,b)>d)return false;
 unsigned key=(((a<<10)|b)<<5)+d; // use unsigned shift for the 24-bit cell pair
 auto it=memo.find(key);if(it!=memo.end())return it->second;
 for(int r=0;r<2;++r){
  int v=r?a:b;
  for(int s=(v-1)&v;s>(s^v);s=(s-1)&v){
   int t=s^v,x1=r?s:a,y1=r?b:s,x2=r?t:a,y2=r?b:t;
   int low=lower(x1,y1),high=d-lower(x2,y2);
   for(int k=low;k<=high;++k)if(fit(x1,y1,k)&&fit(x2,y2,d-k))return memo[key]=true;
  }
 }
 return memo[key]=false;
}
int main(){
 ifstream f("mono.bin",ios::binary);assert(f.read((char*)M.data(),M.size()));
 vector<int> rows{9,17,18,33,36,40,65,66,68,80,129,132,136,160,7,14,28,34,48,72,96,130,144,192};
 vector<int> sig;
 for(int i=0;i<8;++i){int h=0;for(int j=0;j<24;++j)h|=((rows[j]>>i)&1)<<j;sig.push_back(h);}
 int total=0,candidates=0;set<pair<int,int>> surviving;
 for(int i=0;i<8;++i)for(int j=0;j<i;++j)for(int h:{sig[i]|sig[j],sig[i]&sig[j]}){
  if(find(sig.begin(),sig.end(),h)!=sig.end())continue;
  sig.push_back(h);
  for(int l=0;l<9;++l)for(int m=0;m<l;++m)for(int g:{sig[l]|sig[m],sig[l]&sig[m]}){
   if(find(sig.begin(),sig.end(),g)!=sig.end())continue;
   ++total;
   rp[0]=h&R;rn[0]=h>>14;rp[1]=g&R;rn[1]=g>>14;
   for(int z=0;z<4;++z){ps[z]=R;ns[z]=C;
    for(int u=0;u<2;++u)if(z>>u&1)ns[z]&=rn[u];else ps[z]&=~rp[u];}
   int reads=l==8?3:4;
   if(reads+fixboth(R,C)>13)continue;
   ++candidates;memo.clear();if(fit(R,C,13))surviving.insert(minmax(h,g));
  }
  sig.pop_back();
 }
 cout<<"normalized programs "<<total<<"; screened candidates "<<candidates<<"; distinct passing label pairs "<<surviving.size()<<endl;
 for(auto z:surviving)cout<<z.first<<" "<<z.second<<endl;
}

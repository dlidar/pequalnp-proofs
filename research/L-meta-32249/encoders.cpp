// Enumerate unordered sets of jointly available nonraw functions on four inputs.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using U=uint64_t;
struct Query{int t;vector<int> raw,need;int best=100;};
int main(int argc,char**argv){
 const int cap=argc>1?stoi(argv[1]):6;assert(cap<=7);
 vector<int> tt;unordered_map<int,int> id;
 auto add=[&](int t){if(!id.count(t)){id[t]=tt.size()+1;tt.push_back(t);}};
 for(int i=0;i<4;++i){int t=0;for(int x=0;x<16;++x)if(x>>i&1)t|=1<<x;add(t);}
 for(size_t i=0;i<tt.size();++i)for(size_t j=0;j<i;++j){add(tt[i]&tt[j]);add(tt[i]|tt[j]);}
 assert(tt.size()==166);
 int op[167][167][2]={};for(int i=1;i<=166;++i)for(int j=1;j<=166;++j){op[i][j][0]=id.at(tt[i-1]&tt[j-1]);op[i][j][1]=id.at(tt[i-1]|tt[j-1]);}
 vector<Query> qs;int t,n;
 while(cin>>t>>n){Query q;q.t=t;for(int i=0;i<n;++i){int w;cin>>w;q.raw.push_back(w);int j=id.at(w);if(j>4)q.need.push_back(j);}qs.push_back(q);}
 array<vector<int>,167> by;
 for(int i=0;i<(int)qs.size();++i)for(int j:qs[i].need)by[j].push_back(i);
 unordered_set<U> prev{0};
 for(int c=1;c<=cap;++c){
  unordered_set<U> next;
  for(U key:prev){int avail[12]={1,2,3,4};bool has[167]={};for(int i=1;i<=4;++i)has[i]=true;
   for(int i=0;i<c-1;++i){int j=(key>>(8*i))&255;avail[4+i]=j;has[j]=true;}
   bool tried[167]={};
   for(int i=0;i<c+3;++i)for(int j=0;j<i;++j)for(int z:op[avail[i]][avail[j]]){
    if(has[z]||tried[z])continue;
    tried[z]=true;
    for(int q:by[z])if(qs[q].best>c){
      bool ok=true;for(int k:qs[q].need)if(k!=z&&!has[k])ok=false;
      if(ok)qs[q].best=c;
    }
    if(c<cap){
     int k=0;while(k<c-1 && avail[4+k]<z)++k;
     U low=(U(1)<<(8*k))-1;next.insert((key&low)|(U(z)<<(8*k))|((key&~low)<<8));
    }
   }
  }
  cerr<<c<<" reachable "<<next.size()<<" queries solved "<<count_if(qs.begin(),qs.end(),[&](auto&q){return q.best<=c;})<<endl;
  prev.swap(next);
 }
 for(auto&q:qs){cout<<q.t<<" "<<q.best;for(int w:q.raw)cout<<" "<<w;cout<<"\n";}
}

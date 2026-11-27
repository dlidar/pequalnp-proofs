// An independent enumerator using the positive and negative endpoints of each wire's private pairs.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_set>
#include <vector>
using namespace std;
using U=uint64_t;
struct State{vector<U> sig;bool operator==(State const&o)const{return sig==o.sig;}};
struct Hash{size_t operator()(State const&s)const{U h=0;for(U x:s.sig)h=(h^(x+0x9e3779b9+(h<<6)+(h>>2)));return h;}};
using Set=unordered_set<State,Hash>;
struct Gate{U a,b,w;bool join;};
vector<Gate> path;
int npos,nneg;U pos,neg;uint64_t visited=0,rootcount=0;
bool walk(vector<U> const&w,int k,vector<Set>&memo,int level){
 int n=w.size();
 if(binary_search(w.begin(),w.end(),pos))return true;
 if(!k||n>k+1)return false;
 // Close only after exploring children; k strictly decreases so there are no cycles.
 if(memo[k].contains(State{w}))return false;
 visited++;
 array<U,32> demandP{},demandN{},bits{},pre{};
 for(int p=0;p<npos;p++){
  U row=U(1)<<p;pre[0]=neg;
  for(int t=0;t<n;t++){bits[t]=(w[t]&row)?w[t]:neg;pre[t+1]=pre[t]&bits[t];}
  if(pre[n])return false;
  U suffix=neg;
  for(int t=n;t-->0;){U priv=pre[t]&suffix;if(priv){demandP[t]|=row;demandN[t]|=priv;}suffix&=bits[t];}
 }
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
  for(bool join:{false,true}){
   U v=join?(w[a]|w[b]):(w[a]&w[b]);
   if(v==0||v==(pos|neg)||binary_search(w.begin(),w.end(),v))continue;
   bool dropA=join?!(demandN[a]&w[b]):!(demandP[a]&~w[b]);
   bool dropB=join?!(demandN[b]&w[a]):!(demandP[b]&~w[a]);
   for(int take:{3,2,1,0}){
    if((take&1)&&!dropA)continue;if((take&2)&&!dropB)continue;
    if(n+1-popcount(unsigned(take))>k)continue;
    vector<U> next;next.reserve(n+1);
    for(int i=0;i<n;i++)if(!(i==a&&(take&1))&&!(i==b&&(take&2)))next.push_back(w[i]);
    next.insert(lower_bound(next.begin(),next.end(),v),v);
    path.push_back({w[a],w[b],v,join});
    if(level==0){for(auto&s:memo)s.clear();rootcount++;}
    if(walk(next,k-1,memo,level+1))return true;
    path.pop_back();
   }
  }
 }
 if(n>=2 && level>0)memo[k].insert(State{w});return false;
}
int main(int argc,char**argv){
 if(argc!=3)return 2;
 ifstream f(argv[1]);int count;f>>npos>>nneg>>count;
 if(!f||count>=30||npos+nneg>=63)return 2;
 pos=(U(1)<<npos)-1;neg=((U(1)<<nneg)-1)<<npos;
 vector<U> s(count);for(U&v:s)f>>v;
 int k=stoi(argv[2]);vector<Set> memo(k+1);
 for(unsigned m=1;m<(1u<<count);m++){
  if(popcount(m)>k+1)continue;
  vector<U> w;
  for(int i=0;i<count;i++)if(m>>i&1)w.push_back(s[i]);sort(w.begin(),w.end());
  if(walk(w,k,memo,0)){
   cout<<"SAT "<<path.size()<<" nodes "<<visited<<endl;
   for(auto g:path)cout<<(g.join?"o ":"a ")<<g.a<<" "<<g.b<<" "<<g.w<<"\n";
   return 0;
  }
 }
 cout<<"UNSAT "<<k<<" nodes "<<visited<<" root moves "<<rootcount<<endl;
}

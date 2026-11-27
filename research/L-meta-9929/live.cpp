// Exact search of complemented-edge AND networks. Each frontier lists just
// the signals which still have a consumer. Output complement has zero cost.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using W=std::uint64_t;
constexpr W target=36240869367020798ULL;
W norm(W w){return w&1?~w:w;}
struct Step{W a,b,result;unsigned keep;};
std::vector<Step> path;
unsigned long long visited[16]={},splitCount[16]={};
bool separates(const std::vector<W>&s){
  for(W pos=target;pos;pos&=pos-1){
    int row=__builtin_ctzll(pos);W similar=~target;
    for(W v:s){similar&=(v>>row&1)?v:~v;if(!similar)break;}
    if(similar)return false;
  }
  return true;
}
bool solve(const std::vector<W>&s,int left){
  if(s.size()==1)return s.front()==target;
  if(!left || int(s.size())>left+1)return false;
  ++visited[left];
  int slack=left+1-int(s.size());
  for(size_t i=0;i<s.size();++i)for(size_t j=i+1;j<s.size();++j){
    for(W a:{s[i],~s[i]})for(W b:{s[j],~s[j]}){
      W v=norm(a&b);
      if(!v||std::find(s.begin(),s.end(),v)!=s.end())continue;
      for(unsigned keep=0;keep<4;++keep){
        if(__builtin_popcount(keep)>slack)continue;
        std::vector<W> next;next.reserve(s.size()+1);
        for(size_t k=0;k<s.size();++k){
          if((k==i&&!(keep&1))||(k==j&&!(keep&2)))continue;
          next.push_back(s[k]);}
        next.push_back(v);
        if(keep!=3&&!separates(next))continue;
        ++splitCount[left];path.push_back({a,b,v,keep});
        if(solve(next,left-1))return true;
        path.pop_back();
      }
    }
  }
  return false;
}
int main(int argc,char**argv){
  int n=argc>1?std::stoi(argv[1]):8;
  if(n<1||n>9)return 2;
  std::vector<W> raw(6);for(int j=0;j<6;++j)for(int r=0;r<64;++r)if(r>>j&1)raw[j]|=W(1)<<r;
  bool found=solve(raw,n);
  std::cout<<"budget "<<n<<" witness "<<found<<'\n';
  for(auto x:path)std::cout<<x.a<<' '<<x.b<<' '<<x.result<<' '<<x.keep<<'\n';
  for(int i=1;i<=n;++i)std::cout<<i<<" states "<<visited[i]<<" retained "<<splitCount[i]<<'\n';
}

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
#include <unordered_map>
using W=std::uint64_t;
using S=std::vector<W>;
constexpr W target=36240869367020798ULL;
bool separates(const S&s,int t){
  for(W pos=target;pos;pos&=pos-1){
    int row=__builtin_ctzll(pos);W similar=~target;
    for(W v:s){if(v>>row&1)similar&=v;else if(t)similar&=~v;if(!similar)break;}
    if(similar)return false;
  }
  return true;
}
struct key{std::array<W,12> v{};int k=0,t=0;bool operator==(const key&o)const{return v==o.v&&k==o.k&&t==o.t;}};
struct hash{size_t operator()(const key&a)const{W h=a.k*19+a.t;for(W v:a.v){v=(v^(v>>30))*0xbf58476d1ce4e5b9ULL;h=(h^(v^(v>>27)))*0x94d049bb133111ebULL;}return h^(h>>32);}};
std::unordered_map<key,W,hash> cache;
W work=0;
W cost(S s,int k,int t){
 if(!k)return 1;
 std::sort(s.begin(),s.end());key z;std::copy(s.begin(),s.end(),z.v.begin());z.k=k;z.t=t;
 auto it=cache.find(z);if(it!=cache.end())return it->second;
 ++work;if(work%100000==0)std::cerr<<work<<'\n';
 W out=1;int e=k+1-t-int(s.size());assert(e>=0);
 auto add=[&](S ch,int u){if(separates(ch,u))out+=cost(ch,k-1,u);};
 for(size_t a=0;a<s.size();++a){
   if(t&&!std::binary_search(s.begin(),s.end(),~s[a])){
     S ch=s;ch[a]=~s[a];add(ch,t-1);
     if(e>0){ch.push_back(s[a]);add(ch,t-1);}
   }
   for(size_t b=a+1;b<s.size();++b)for(auto v:{s[a]&s[b],s[a]|s[b]}){
     if(!v||!~v||std::binary_search(s.begin(),s.end(),v))continue;
     S x=s;x[a]=v;x.erase(x.begin()+b);
     add(x,t);
     if(e>0){x.push_back(s[a]);add(x,t);x.back()=s[b];add(x,t);}
     if(e>1){x.push_back(s[a]);add(x,t);}
   }
 }
 if(cache.size()<1000000)cache[z]=out;
 return out;
}
extern "C" W treecharge(int k,int t,int n,W const* x){return cost(S(x,x+n),k,t);}
int main(int argc,char**argv){
 S s(6);for(int j=0;j<6;++j)for(int i=0;i<64;++i)if(i>>j&1)s[j]|=W(1)<<i;
 for(int t:{6,5,4,3,2,1}){auto c=cost(s,11,t);std::cout<<t<<' '<<c<<' '<<work<<std::endl;}
}

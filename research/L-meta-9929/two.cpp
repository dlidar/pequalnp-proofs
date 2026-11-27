#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using Word = std::uint64_t;
using Wires = std::vector<Word>;
constexpr Word goal=36240869367020798ULL;
struct Test { Word zero,one; bool fits(Word x)const{return !(x&zero) && (x&one)==one;} };
constexpr Test firstTest{0x76006e2a17ULL,0x80e8a80088000000ULL};
constexpr Test secondTest{0xe8a80088000017ULL,0x80000076006e2a00ULL};
unsigned long long counts[3][20]={};
bool found=false;
// In a shortest circuit every nonconstant binary output is fresh. Among
// topological orders within one monotone block, use a lexicographically
// least one. Independent adjacent gates cannot be in decreasing order.
template<class F> void extend(Wires &w, bool ordered, F consume){
  auto n=w.size();
  Word prev=w.back();
  for(size_t i=0;i<n;++i)for(size_t j=i+1;j<n;++j){
    auto a=w[i],b=w[j];
    for(auto v:{a&b,a|b}){
      if(!v || v==~Word{0} || (ordered && j+1<n && v<prev))continue;
      if(std::find(w.begin(),w.end(),v)!=w.end())continue;
      w.push_back(v);consume(v);w.pop_back();
    }
  }
}
void finish(Wires &w,int budget,int used){
  if(found || budget==0)return;
  extend(w,used!=0,[&](Word v){
    if(v==goal){found=true;for(auto t:w)std::cout<<t<<' ';std::cout<<'\n';return;}
    finish(w,budget-1,used+1);
  });
}
void middle(Wires &w,int left,int used){
  if(found || left<=3)return; // keep 1 slot for second NOT and >=2 binary gates after it
  extend(w,used!=0,[&](Word v){
    if(used+1>=2 && secondTest.fits(v)){
      ++counts[1][w.size()-6];
      w.push_back(~v);finish(w,left-2,0);w.pop_back();
    }
    middle(w,left-1,used+1);
  });
}
void prefix(Wires &w,int budget,int used){
  if(found || budget<=6)return; // keep 2 NOTs, >=2 intermediate and >=2 final binary gates
  extend(w,used!=0,[&](Word v){
    if(firstTest.fits(v)){
      ++counts[0][used+1];w.push_back(~v);middle(w,budget-2,0);w.pop_back();
    }
    prefix(w,budget-1,used+1);
  });
}
int main(int argc,char**argv){
  int bound=argc==2?std::stoi(argv[1]):11;
  if(bound<1 || bound>13)return 2;
  Wires w(6);w.reserve(24);
  for(int i=0;i<6;++i)for(int k=0;k<64;++k)if(k>>i&1)w[i]|=Word{1}<<k;
  prefix(w,bound,0);
  std::cout<<"found "<<found<<'\n';
  for(int k=0;k<2;++k){for(int i=0;i<20;++i)if(counts[k][i])std::cout<<"stage "<<k<<" at "<<i<<" : "<<counts[k][i]<<'\n';}
}

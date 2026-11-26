// Count full truth-table differences for every single bipartite edge toggle.
// Endpoints must both be on; all their other neighbours must be off.
#include <array>
#include <bit>
#include <cstdio>
#include <vector>
using Mask=unsigned;
using Count=unsigned long long;
int main(){
 std::array<Mask,21> rows{};
 for(auto& r:rows) if(scanf("%u",&r)!=1)return 1;
 for(unsigned p=0;p<21;p++)for(unsigned l=0;l<21;l++){
  Mask forbidden=rows[p]|(1u<<l);
  std::vector<Mask> unions{0};
  for(unsigned q=0;q<21;q++)if(q!=p && !(rows[q]&(1u<<l))){
    auto size=unions.size();
    for(unsigned k=0;k<size;k++)unions.push_back(unions[k]|rows[q]);
  }
  Count total=0;
  for(auto z:unions) total+=1ull<<(21-std::popcount(z|forbidden));
  printf("%u %u %u %llu\n",p,l,(rows[p]>>l)&1,total);
 }
}

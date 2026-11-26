#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using Word=std::uint64_t;
using Mask=std::array<Word,10>;
std::array<Mask,600> later{};
std::array<std::uint64_t,26> count{};
void extend(Mask s,int depth){
  ++count[depth];
  for(int k=0;k<10;k++) while(s[k]){
    int i=64*k+std::countr_zero(s[k]);s[k]&=s[k]-1;
    Mask t{};for(int j=k;j<10;j++)t[j]=s[j]&later[i][j];
    extend(t,depth+1);
  }
}
int main(){
  std::array<unsigned,25> rows;for(auto& r:rows)std::cin>>r;
  std::vector<std::pair<int,int>> zero;
  for(int i=0;i<25;i++)for(int j=0;j<30;j++)if(!(rows[i]>>j&1))zero.emplace_back(i,j);
  if(zero.size()!=600)return 1;
  Mask all{};
  for(int i=0;i<600;i++){
    all[i/64]|=Word(1)<<(i%64);
    for(int j=i+1;j<600;j++){
      auto [p,l]=zero[i];auto [q,m]=zero[j];
      if((rows[p]>>m|rows[q]>>l)&1)later[i][j/64]|=Word(1)<<(j%64);
    }
  }
  extend(all,0);
  for(int n=0;n<=25;n++)if(count[n])std::cout<<n<<" "<<count[n]<<"\n";
}

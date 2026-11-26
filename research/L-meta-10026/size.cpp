#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <algorithm>
using namespace std;
int main() {
  array<uint32_t,25> row{};
  for(auto& v:row)cin>>v;
  array<uint32_t,4096> lo{},samples{};
  array<uint32_t,8192> hi{};
  for(unsigned i=1;i<lo.size();++i)lo[i]=lo[i&(i-1)]|row[countr_zero(i)];
  for(unsigned i=1;i<hi.size();++i)hi[i]=hi[i&(i-1)]|row[12+countr_zero(i)];
  array<int,26> largest{};array<unsigned,26> example{},count{};
  for(unsigned i=0;i<hi.size();++i)for(unsigned j=0;j<lo.size();++j){
    unsigned m=(i<<12)|j, k=popcount(m);
    int usable=30-popcount(hi[i]|lo[j]);
    if(usable>largest[k]){largest[k]=usable;example[k]=m;count[k]=0;}
    if(usable==largest[k])++count[k];
  }
  for(unsigned k=1;k<=25;++k)cout<<k<<" "<<largest[k]<<" "<<count[k]<<" "<<example[k]<<"\n";
}

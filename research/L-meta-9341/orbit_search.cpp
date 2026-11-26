#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <optional>
#include <string>
#include <vector>
using Word=uint64_t;
struct Mask { Word lo,hi; };
int count(Mask a){return std::popcount(a.lo)+std::popcount(a.hi);}
Mask minusMask(Mask a,Mask b){return {a.lo&~b.lo,a.hi&~b.hi};}
int gain(Mask a,Mask b){return std::popcount(a.lo&b.lo)+std::popcount(a.hi&b.hi);}
struct Box { Mask mask; int id; };
std::vector<Box> triples,singles;
std::vector<int> chosen;
std::array<uint64_t,12> nodes{};
bool solve(Mask rem,int slots){
 int cells=count(rem);
 if(!cells)return true;
 if(!slots)return false;
 ++nodes[slots];
 int limit=(cells+slots-1)/slots;
 for(const auto &b:triples){
  if(count(b.mask)<limit)break;
  if(gain(b.mask,rem)<limit)continue;
  chosen.push_back(b.id);
  if(solve(minusMask(rem,b.mask),slots-1))return true;
  chosen.pop_back();
 }
 return false;
}
int main(int argc,char**argv){
 if(argc<4||argc>5)return 2;
 const int width=std::stoi(argv[1]), budget=std::stoi(argv[2]), cost=std::stoi(argv[3]);
 Mask all{width>=64?~Word(0):(Word(1)<<width)-1,width<=64?0:(Word(1)<<(width-64))-1};
 if(argc==5){unsigned bit=std::stoul(argv[4]);if(bit<64)all.lo&=~(Word(1)<<bit);else all.hi&=~(Word(1)<<(bit-64));}
 int id,n;Word lo,hi;
 while(std::cin>>id>>n>>lo>>hi)(n==1?singles:triples).push_back({{lo,hi},id});
 std::sort(triples.begin(),triples.end(),[](Box a,Box b){return count(a.mask)>count(b.mask);});
 for(unsigned bits=0;bits<(1u<<singles.size());++bits){
  int ns=std::popcount(bits);if(ns>budget)continue;
  int slots=(budget-ns)/cost;
  // Extra singleton choices are harmless. Test only maximal singleton counts at each triple budget.
  if(ns<int(singles.size()) && (budget-ns)%cost!=0)continue;
  Mask rem=all;chosen.clear();
  for(unsigned i=0;i<singles.size();++i)if((bits>>i)&1){
   rem=minusMask(rem,singles[i].mask);chosen.push_back(singles[i].id);
  }
  if(solve(rem,slots)){std::cout<<"COVER";for(int x:chosen)std::cout<<" "<<x;std::cout<<"\n";return 0;}
 }
 std::cout<<"EXHAUSTED";for(int k=0;k<=budget/cost;++k)std::cout<<" "<<nodes[k];std::cout<<"\n";
}

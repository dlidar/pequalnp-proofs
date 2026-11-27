// Exact number of leaves of a separating AND/OR formula on subsets of
// positive and negative rows. A root OR partitions positive tests; a root
// AND partitions negative tests. Constants are permitted as leaf signals.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
using namespace std;
const vector<pair<int,int>> edges={{0,3},{1,4},{0,5},{1,5},{2,5},{0,6},{2,6},{3,6},{0,7},{1,7},{2,7},{3,7},{5,7},{6,7}};
bool target(int x){for(auto [i,j]:edges)if((x>>i)&(x>>j)&1)return true;return false;}
int main(int argc,char**argv){
 vector<int> P,N;for(auto [i,j]:edges)P.push_back((1<<i)|(1<<j));
 for(int x=0;x<256;++x)if(!target(x)){bool maximal=true;for(int j=0;j<8;++j)if(!(x>>j&1)&&!target(x|(1<<j)))maximal=false;if(maximal)N.push_back(x);}
 int M=1<<P.size(),K=1<<N.size();vector<pair<int,int>> labels;
 for(int i=0;i<8;++i){int a=0,b=0;for(int j=0;j<(int)P.size();++j)a|=((P[j]>>i)&1)<<j;for(int j=0;j<(int)N.size();++j)b|=(!(N[j]>>i&1))<<j;labels.emplace_back(a,b);}
 if(argc>2 && string(argv[2])=="signed")for(int i=0;i<8;++i)labels.emplace_back(M-1-labels[i].first,K-1-labels[i].second);
 vector<uint8_t> cost(M*K,1);array<int,80>hist{};
 for(int a=0;a<M;++a)for(int b=0;b<K;++b){int m=1;
   if(a&&b&&none_of(labels.begin(),labels.end(),[&](auto lab){return !(a&~lab.first)&&!(b&~lab.second);})){
    m=70;for(int s=(a-1)&a;s;s=(s-1)&a){if(s<(a^s))break;m=min(m,(int)cost[s*K+b]+cost[(a^s)*K+b]);if(m==2)break;}
    if(m>2)for(int s=(b-1)&b;s;s=(s-1)&b){if(s<(b^s))break;m=min(m,(int)cost[a*K+s]+cost[a*K+(b^s)]);if(m==2)break;}
   }cost[a*K+b]=m;++hist[m];
 }
 ofstream o(argv[1],ios::binary);o.write((const char*)cost.data(),cost.size());
 cout<<"positive "<<P.size()<<" negative "<<N.size()<<" full minimum leaves "<<(int)cost.back()<<"\n";
 for(int i=1;i<80;i++)if(hist[i])cout<<i<<' '<<hist[i]<<'\n';
}

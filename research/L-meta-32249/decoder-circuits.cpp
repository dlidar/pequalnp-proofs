// All reduced monotone circuits on five raw signals through five gates.
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
using namespace std;
using U=uint32_t; array<U,11> wires; unordered_map<U,int> cost;
void visit(int n,int limit){
 int k=n-5;if(k){auto [it,inserted]=cost.emplace(wires[n-1],k);if(!inserted)it->second=min(k,it->second);}
 if(k==limit)return;
 int lastStart=k+1==limit && k>0?n-1:1;
 for(int j=lastStart;j<n;++j)for(int i=0;i<j;++i)for(U w:{wires[i]&wires[j],wires[i]|wires[j]}){
  bool fresh=true;for(int a=0;a<n;++a)if(wires[a]==w){fresh=false;break;}
  if(fresh){wires[n]=w;visit(n+1,limit);}
 }
}
int main(){for(int j=0;j<5;++j){U t=0;for(int x=0;x<32;++x)if(x>>j&1)t|=U(1)<<x;wires[j]=t;cost[t]=0;}visit(5,5);
 for(auto [t,k]:cost)cout<<t<<" "<<k<<"\n";
}

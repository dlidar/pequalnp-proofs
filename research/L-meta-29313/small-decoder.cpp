#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
int main(){
 int r,c;while(cin>>r>>c){
   assert(r<=17 && c<=10 && r+c<=23);int p[512],q[512];
   for(int i=0;i<r;i++)cin>>p[i];for(int j=0;j<c;j++)cin>>q[j];
   int A=1<<r,B=1<<c;array<int,9> L{},R{};
   for(int t=0;t<9;t++){for(int i=0;i<r;i++)L[t]|=(p[i]>>t&1)<<i;for(int j=0;j<c;j++)R[t]|=(1-(q[j]>>t&1))<<j;}
   vector<uint8_t>d(A*B,1);
   for(int a=1;a<A;a++)for(int b=1;b<B;b++){
    bool leaf=false;for(int t=0;t<9;t++)if(!(a&~L[t])&&!(b&~R[t])){leaf=true;break;}if(leaf)continue;
    int best=40;
    for(int s=(b-1)&b;s>(b^s);s=(s-1)&b){best=min(best,d[a*B+s]+d[a*B+(b^s)]);if(best==2)break;}
    if(best>2)for(int s=(a-1)&a;s>(a^s);s=(s-1)&a){best=min(best,d[s*B+b]+d[(a^s)*B+b]);if(best==2)break;}
    d[a*B+b]=best;
   }
   cout<<int(d.back())<<endl;
 }
}

// Exact monotone decoder for each preliminary raw AND/OR, with arbitrary fanout.
// The enlarged input list remains monotone in the original eight variables.
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <utility>
#include <vector>
using namespace std;
const vector<int> pos={17,33,34,36,65,66,80,96,130,132,136,144,192};
bool graph(int x){for(int e:pos)if((x&e)==e)return true;return false;}
int main(){
  vector<int> neg;
  for(int x=0;x<256;x++)if(!graph(x)){
    bool maximal=true;
    for(int i=0;i<8;i++)if(!(x>>i&1)&&!graph(x|1<<i))maximal=false;
    if(maximal)neg.push_back(x);
  }
  assert(neg.size()==6);
  for(int op=0;op<2;op++)for(int i=0;i<8;i++)for(int j=i+1;j<8;j++){
    auto sig=[&](int x,int k){if(k<8)return (x>>k)&1;
      return op?(((x>>i)|(x>>j))&1):(((x>>i)&(x>>j))&1);};
    array<int,9> rp{},cn{};
    for(int t=0;t<9;t++){
      for(int r=0;r<13;r++)rp[t]|=sig(pos[r],t)<<r;
      for(int c=0;c<6;c++)cn[t]|=(1-sig(neg[c],t))<<c;
    }
    vector<unsigned char>d(8192*64,1);
    for(int a=1;a<8192;a++)for(int b=1;b<64;b++){
      bool atom=false;for(int t=0;t<9;t++)if(!(a&~rp[t])&&!(b&~cn[t]))atom=true;
      if(atom)continue;
      int u=30;
      auto&v=d[64*a+b];
      for(int t=(b-1)&b;t>(b^t);t=(t-1)&b)u=min(u,d[64*a+t]+d[64*a+(b^t)]);
      if(u>2)for(int t=(a-1)&a;t>(a^t);t=(t-1)&a){u=min(u,d[64*t+b]+d[64*(a^t)+b]);if(u==2)break;}
      v=u;
    }
    cout<<(op?"or":"and")<<" "<<i<<" "<<j<<" "<<(int)d.back()<<endl;
  }
}

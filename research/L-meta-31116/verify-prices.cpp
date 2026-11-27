// Verify that every candidate value satisfies both sides of the formula recurrence.
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
int main(){
 const vector<int> p={17,18,33,36,65,66,72,96,129,130,132,144,160,192},n={15,28,42,56,84,136};
 const unsigned w=64;
 vector<unsigned char> cost((1u<<p.size())*w);
 ifstream in("mono.bin",ios::binary);assert(in.read((char*)cost.data(),cost.size()));assert(in.peek()==EOF);
 vector<int> commonP(1u<<p.size(),255),commonN(w,255);
 for(unsigned x=1;x<commonP.size();x++)commonP[x]=commonP[x&(x-1)]&p[__builtin_ctz(x)];
 for(unsigned y=1;y<w;y++)commonN[y]=commonN[y&(y-1)]&~n[__builtin_ctz(y)];
 for(unsigned y=0;y<w;y++)for(unsigned x=0;x<commonP.size();x++){
  unsigned t=cost[x*w+y];bool leaf=!x||!y||(commonP[x]&commonN[y]);
  if(leaf){assert(t==1);continue;}
  assert(t>=2);bool realized=false;
  for(unsigned left=(x-1)&x;left;left=(left-1)&x){
   unsigned v=cost[left*w+y]+cost[(x-left)*w+y];assert(v>=t);realized|=v==t;
  }
  for(unsigned left=(y-1)&y;left;left=(left-1)&y){
   unsigned v=cost[x*w+left]+cost[x*w+y-left];assert(v>=t);realized|=v==t;
  }
  assert(realized);
 }
 cout<<"verified "<<cost.size()<<" optimal formula prices"<<endl;
}

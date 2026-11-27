// Verify all leaf and decomposition inequalities for a supplied integer potential.
// Any formula separating the two index sets needs at least their potential.
#include <cassert>
#include <fstream>
#include <iterator>
#include <vector>
#include <iostream>
using namespace std;
int main(int argc,char** argv) {
  assert(argc==2);
  vector<int> edge={17,33,34,36,65,66,72,80,129,132,144,160};
  auto independent=[&](int x){for(int e:edge)if((x&e)==e)return false;return true;};
  vector<int> neg;
  for(int x=0;x<256;x++)if(independent(x)){
    bool maximal=true;
    for(int i=0;i<8;i++)if(!(x&(1<<i))&&independent(x|(1<<i)))maximal=false;
    if(maximal)neg.push_back(x);
  }
  assert(neg.size()==7);
  ifstream input(argv[1],ios::binary);
  vector<unsigned char> tab{istreambuf_iterator<char>(input),istreambuf_iterator<char>()};
  assert(tab.size()==4096*128);
  auto v=[&](int a,int b){return int(tab.at(128*a+b));};
  for(int a=0;a<4096;a++)for(int b=0;b<128;b++){
    int val=v(a,b);
    assert(val>0);
    int common=255,forbid=0;
    for(int j=0;j<12;j++)if(a&(1<<j))common&=edge[j];
    for(int j=0;j<7;j++)if(b&(1<<j))forbid|=neg[j];
    if(!a||!b||(common&~forbid))assert(val<=1);
    for(int t=a;t;t=(t-1)&a)assert(val<=v(t,b)+v(a^t,b));
    for(int t=b;t;t=(t-1)&b)assert(val<=v(a,t)+v(a,b^t));
  }
  assert(v(4095,127)==15);
  cout<<"verified 524288 subproblems and full lower bound of 15 leaves\n";
}

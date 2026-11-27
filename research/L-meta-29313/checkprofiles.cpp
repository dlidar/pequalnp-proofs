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
  vector<int> edge={17,33,34,36,65,66,80,96,130,132,136,144,192};
  auto independent=[&](int x){for(int e:edge)if((x&e)==e)return false;return true;};
  vector<int> neg;
  for(int x=0;x<256;x++)if(independent(x)){
    bool maximal=true;
    for(int i=0;i<8;i++)if(!(x&(1<<i))&&independent(x|(1<<i)))maximal=false;
    if(maximal)neg.push_back(x);
  }
  assert(neg.size()==6);
  ifstream input(argv[1],ios::binary);
  vector<unsigned char> tab{istreambuf_iterator<char>(input),istreambuf_iterator<char>()};
  assert(tab.size()==8192*64);
  auto v=[&](int a,int b){return int(tab.at(64*a+b));};
  for(int a=0;a<8192;a++)for(int b=0;b<64;b++){
    int val=v(a,b);
    assert(val>0);
    int common=255,forbid=0;
    for(int j=0;j<13;j++)if(a&(1<<j))common&=edge[j];
    for(int j=0;j<6;j++)if(b&(1<<j))forbid|=neg[j];
    bool attains=!a||!b||(common&~forbid);
    if(attains)assert(val==1);
    for(int t=a;t;t=(t-1)&a){int sum=v(t,b)+v(a^t,b);assert(val<=sum);attains|=(sum==val);}
    for(int t=b;t;t=(t-1)&b){int sum=v(a,t)+v(a,b^t);assert(val<=sum);attains|=(sum==val);}
    assert(attains);
  }
  assert(v(8191,63)==15);
  cout<<"verified 524288 subproblems with matching upper bounds and full minimum of 15 leaves\n";
}

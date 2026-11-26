#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <string>
using namespace std;
constexpr unsigned goalMask=2113947;
constexpr int full=(1<<21)-1;
struct Node{int a=-1,b=-1;char op=0;unsigned char neg=0;};
int main(){
 array<int,6> raw{};int goal=0,irow=0;
 for(int i=0;i<6;i++)for(int j=i;j<6;j++,irow++){
  if(uint64_t(goalMask)>>(6*i+j)&1)goal|=1<<irow;
  raw[i]|=1<<irow;raw[j]|=1<<irow;
 }
 array<vector<Node>,2> witness{vector<Node>(1<<21),vector<Node>(1<<21)};
 array<array<vector<int>,15>,2> layers;
 auto add=[&](int h,int dist,int v,int a,int b,char op,int neg){
  if(!witness[h][v].op){witness[h][v]={a,b,op,(unsigned char)neg};layers[h][dist].push_back(v);}
 };
 for(int j=0;j<6;j++)add(0,0,raw[j],j,0,'x',0);
 for(int n=1;n<15;n++){
  for(int x:layers[0][n-1])add(1,n,full^x,x,0,'!',0);
  for(int q=0;q<2;q++)for(int i=0;i<n;i++)for(int k=0;k<=q;k++){
   int j=n-1-i;if(i>j || (i==j && k>q-k))continue;
   for(int a:layers[k][i])for(int b:layers[q-k][j]){
    add(q,n,a&b,a,b,'&',k);add(q,n,a|b,a,b,'|',k);
   }
  }
  if(witness[1][goal].op){
   auto form=[&](auto&& f,int q,int v)->string{
    auto t=witness[q][v];
    if(t.op=='x')return to_string(t.a);
    if(t.op=='!')return "(!"+f(f,0,t.a)+")";
    return "("+f(f,t.neg,t.a)+t.op+f(f,q-t.neg,t.b)+")";
   };
   cout<<"exact one-NOT formula minimum "<<n<<" "<<form(form,1,goal)<<endl;return 0;
  }
  cout<<"size "<<n<<" reached "<<layers[0][n].size()<<" monotone, "<<layers[1][n].size()<<" one-NOT"<<endl;
 }
}

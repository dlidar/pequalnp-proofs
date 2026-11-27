// Exact bounded synthesis of a monotone downstream circuit over selected input signals.
// A state contains the wires with a future reader, including the output as a reader.
#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_set>
#include <vector>
using namespace std;
using Word=uint64_t;
using State=vector<Word>;
struct Hash{size_t operator()(State const&v)const{size_t a=17;for(auto w:v)a=(a^w)*11400714819323198485ull;return a;}};
int P,N;Word target,negatives;uint64_t nodes,pruned;vector<unordered_set<State,Hash>> seen;
bool separates(State const&s){
 for(int i=0;i<P;i++){
  Word common=negatives;
  for(Word w:s)if(w>>i&1){common&=w;if(!common)break;}
  if(common)return false;
 }return true;
}
struct Move{Word a,b,out;char op;};
vector<Move> path;
bool search(State s,int gates){
 if(find(s.begin(),s.end(),target)!=s.end())return true;
 if(!gates || int(s.size())>gates+1)return false;
 sort(s.begin(),s.end());
 if(!seen[gates].insert(s).second)return false;
 nodes++;
 for(int i=0;i<int(s.size());i++)for(int j=0;j<i;j++){
  Word a=s[i],b=s[j];
  for(int op=0;op<2;op++){Word w=op?(a|b):(a&b);
   if(w==0 || w==(target|negatives) || binary_search(s.begin(),s.end(),w))continue;
   for(int keep=0;keep<4;keep++){
    if(int(s.size())-1+popcount(unsigned(keep))>gates)continue;
    State next;
    for(int t=0;t<int(s.size());t++)if((t!=i || (keep&1)) && (t!=j || (keep&2)))next.push_back(s[t]);
    next.push_back(w);
    if(!separates(next)){pruned++;continue;}
    path.push_back({a,b,w,op?'o':'a'});
    if(search(next,gates-1))return true;
    path.pop_back();
   }
  }
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=3)return 2;
 ifstream f(argv[1]);int n;f>>P>>N>>n;if(!f||P+N>=64||n>=30)return 2;
 State all(n);for(auto& w:all)f>>w;
 target=(Word(1)<<P)-1;negatives=((Word(1)<<N)-1)<<P;
 int k=stoi(argv[2]);seen.resize(k+1);
 for(int m=1;m<(1<<n);m++){
  if(popcount(unsigned(m))>k+1)continue;State s;
  for(int i=0;i<n;i++)if(m>>i&1)s.push_back(all[i]);
  if(!separates(s))continue;
  if(search(s,k)){
   cout<<"SAT "<<path.size()<<" nodes "<<nodes<<endl;
   for(auto v:path)cout<<v.op<<" "<<v.a<<" "<<v.b<<" "<<v.out<<"\n";return 0;
  }
 }
 cout<<"UNSAT "<<k<<" nodes "<<nodes<<" pruned "<<pruned<<endl;
}

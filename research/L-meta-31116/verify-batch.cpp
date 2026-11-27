#define BATCH_DIRECT
#include "slow-split.cpp"
#include <filesystem>
int main(int argc,char**argv){
 if(argc!=3)return 2;int k=stoi(argv[2]),id,n;initialBudget=k;seen.resize(k+1);
 ifstream f(argv[1]);if(!f)return 2;int done=0,yes=0;
 while(f>>id>>P>>N>>n){
  if(std::filesystem::exists("lost")||std::filesystem::exists("stop"))return 3;
  target=(Word(1)<<P)-1;negatives=((Word(1)<<N)-1)<<P;State all(n);for(auto&w:all)f>>w;
  bool hit=false;path.clear();for(auto&table:seen)table.clear();
  unsigned compulsory=0;
  for(int i=0;i<n;i++){State without=all;without.erase(without.begin()+i);if(!separates(without))compulsory|=1u<<i;}
  unsigned extra=((1u<<n)-1)^compulsory;
  for(unsigned v=extra;;v=(v-1)&extra){unsigned m=v|compulsory;
   if(m && popcount(m)<=k+1){State s;for(int i=0;i<n;i++)if(m>>i&1)s.push_back(all[i]);
   if(separates(s)&&search(s,k)){hit=true;break;}}if(!v)break;
  }
  if(hit){yes++;cout<<"witness "<<id<<endl;}
  done++;if(done%250==0)cout<<"checked "<<done<<" candidate count "<<yes<<endl;
 }
 cout<<"verified "<<done<<" problems, "<<yes<<" candidates; "<<nodes<<" admitted states"<<endl;
}

#define BATCH_FRONTIERS
#include "fast.cpp"
#include <filesystem>
int main(int argc,char**argv){
 if(argc!=3)return 2;
 int k=stoi(argv[2]),id,count;ifstream f(argv[1]);
 if(!f)return 2;
 uint64_t sum=0;int completed=0,found=0;
 while(f>>id>>npos>>nneg>>count){
  if(std::filesystem::exists("lost")||std::filesystem::exists("stop"))return 3;
  if(count>=30||npos+nneg>=63)return 2;
  pos=(U(1)<<npos)-1;neg=((U(1)<<nneg)-1)<<npos;
  vector<U> features(count);for(auto& v:features)f>>v;
  path.clear();visited=rootcount=0;vector<Set> memo(k+1);
  bool sat=false;
  for(unsigned mask=1;mask<(1u<<count)&&!sat;mask++)if(popcount(mask)<=k+1){
   vector<U> w;for(int i=0;i<count;i++)if(mask>>i&1)w.push_back(features[i]);sort(w.begin(),w.end());
   sat=walk(w,k,memo,0);
  }
  if(sat){found++;cout<<"SAT "<<id<<endl;for(auto g:path)cout<<(g.join?"o ":"a ")<<g.a<<" "<<g.b<<" "<<g.w<<"\n";}
  sum+=visited;completed++;if(completed%250==0)cout<<"checked "<<completed<<" cases "<<found<<" candidates"<<endl;
 }
 cout<<"finished "<<completed<<" cases "<<found<<" candidates "<<sum<<" states"<<endl;
}

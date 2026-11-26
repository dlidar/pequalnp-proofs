#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>

struct Gate { int op,a,b; };
using Grid=std::uint64_t;
using Circuit=std::array<Gate,23>;
constexpr Grid target=14466700110149527140ULL;
std::array<Grid,39> initial{};
int score(const Circuit& g) {
  auto x=initial;
  for(int i=0;i<23;i++) {
    auto t=g[i]; x[16+i]=t.op?(x[t.a]|x[t.b]):(x[t.a]&x[t.b]);
  }
  return std::popcount(x.back()^target);
}
void save(const Circuit& g,const char* file) {
  std::ofstream out(file);out<<"[";
  for(int i=0;i<23;++i){auto t=g[i];if(i)out<<",";out<<"[\""<<(t.op?"or":"and")<<"\","<<t.a<<","<<t.b<<"]";}
  out<<"]\n";
}
int main(){
  for(int i=0;i<64;i++) {initial[i/8]|=1ULL<<i;initial[8+i%8]|=1ULL<<i;}
  std::array<Gate,24> source;
  std::ifstream f("q24.txt");for(auto& g:source)if(!(f>>g.op>>g.a>>g.b))return 2;
  long long tested=0;int best=65;
  for(int cut=0;cut<24;++cut)for(int repl=0;repl<16+cut;++repl){
    Circuit g;
    auto wire=[&](int i){return i==16+cut?repl:i-(i>16+cut);};
    for(int j=0,k=0;j<24;++j)if(j!=cut){auto t=source[j];g[k++]={t.op,wire(t.a),wire(t.b)};}
    // Deleting the output selects an earlier wire. Pad unused slots with identity.
    if(cut==23 && repl!=38)g.back()={1,repl,repl};
    for(int j=0;j<23;++j){
      auto orig=g[j];
      for(int op=0;op<2;++op)for(int a=0;a<16+j;++a)for(int b=a;b<16+j;++b) {
        g[j]={op,a,b};int err=score(g);++tested;
        if(err<best){best=err;save(g,"edit-best.json");std::cout<<"best "<<best<<" tested "<<tested<<std::endl;}
        if(err==0){save(g,"witness.json");return 0;}
      }
      g[j]=orig;
    }
  }
  std::cout<<"finished "<<tested<<" minimum "<<best<<std::endl;
}

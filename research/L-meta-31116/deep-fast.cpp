// Enumerate connected prefix DAGs in canonical topological order, omitting duplicate Boolean signals.
#define BATCH_FRONTIERS
#include "fast.cpp"
#include <filesystem>
using Table=array<U,4>;
struct Op{int a,b;bool join;};
vector<Table> t;vector<Op> prog;bool truth[256];int depth;
uint64_t examined=0,essentialPruned=0,solved=0,models=0;
using Pivots=array<Table,8>;
array<Pivots,14> missing{};
bool get(Table const&w,int x){return w[x/64]>>(x%64)&1;}
void update(Table const&v,int k){
 for(int i=0;i<8;i++){int shift=1<<i;
  for(int a=0;a<4;a++){
   U ref;
   if(shift<64)ref=(v[a]<<shift)|(a?(v[a-1]>>(64-shift)):0);
   else ref=(a>=shift/64)?v[a-shift/64]:0;
   missing[k+1][i][a]=missing[k][i][a]&~(v[a]^ref);
  }
 }
}
void check(){
 examined++;int required=0;
 for(int i=0;i<8;i++)required+=bool(missing[depth][i][0]|missing[depth][i][1]|missing[depth][i][2]|missing[depth][i][3]);
 int budget=12-depth;
 // Every saving circuit uses the complemented wire; removing an unused inverter gives a monotone circuit.
 if(required>budget){essentialPruned++;return;}
 const Table h=t.back();vector<int> p,n;
 for(int x=0;x<256;x++){
  bool maximal=true;
  for(int i=0;i<8;i++)if(((x>>i)&1)==int(truth[x])){
   int y=x^(1<<i);if(truth[y]==truth[x]&&get(h,y)==get(h,x))maximal=false;
  }
  if(maximal)(truth[x]?p:n).push_back(x);
 }
 if(p.size()+n.size()>62){while(p.size()+n.size()>62){if(p.size()>n.size())p.pop_back();else n.pop_back();}}
 npos=p.size();nneg=n.size();vector<int> rows=p;rows.insert(rows.end(),n.begin(),n.end());
 pos=(U(1)<<npos)-1;neg=((U(1)<<nneg)-1)<<npos;
 vector<U> all;for(auto &tab:t){U v=0;for(unsigned i=0;i<rows.size();i++)if(get(tab,rows[i]))v|=U(1)<<i;all.push_back(v);}
 all.push_back(all.back()^(pos|neg));
 int count=all.size();unsigned must=1u<<(count-1);
 for(int i=0;i<npos;i++)for(int j=0;j<nneg;j++){
  unsigned cut=0;for(int l=0;l<count;l++)if((all[l]>>i&1)&&!(all[l]>>(npos+j)&1))cut|=1u<<l;
  if(popcount(cut)==1)must|=cut;
 }
 if(popcount(must)>budget+1){essentialPruned++;return;}solved++;
 unsigned extra=((1u<<count)-1)^must;vector<Set> memo(budget+1);
 for(unsigned s=extra;;s=(s-1)&extra){
  unsigned mask=must|s;
  if(popcount(mask)<=budget+1){vector<U> w;for(int i=0;i<count;i++)if(mask>>i&1)w.push_back(all[i]);sort(w.begin(),w.end());path.clear();
   if(walk(w,budget,memo,0)){models++;cout<<"candidate";for(auto z:prog)cout<<" "<<z.a<<","<<z.b<<","<<z.join;cout<<endl;return;}
  }
  if(!s)break;
 }
}
void gen(unsigned open){
 int k=prog.size(),n=t.size();if(k<=1&&(filesystem::exists("stop")||filesystem::exists("lost")))exit(3);
 if(k==depth){check();return;}
 int remaining=depth-k-1;
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
  auto next=(open&~((1u<<a)|(1u<<b)))|(1u<<n);
  if(popcount(next)>remaining+1)continue;
  for(bool j:{false,true}){
   Table v;for(int l=0;l<4;l++)v[l]=j?(t[a][l]|t[b][l]):(t[a][l]&t[b][l]);
   if(find(t.begin(),t.end(),v)!=t.end())continue;
   bool canonical=true;for(int m=max(8,b+1);m<n;m++)if(v<t[m])canonical=false;
   if(!canonical)continue;
   update(v,k);
   t.push_back(v);prog.push_back({a,b,j});gen(next);prog.pop_back();t.pop_back();
  }
 }
 if(k==1)cout<<"processed first gate; prefixes "<<examined<<" candidates "<<models<<endl;
 if(k==0)cout<<"complete depth "<<depth<<" prefixes "<<examined<<" support exclusions "<<essentialPruned<<" decoder searches "<<solved<<" candidates "<<models<<endl;
}
int main(int argc,char**argv){
 if(argc!=2)return 2;depth=stoi(argv[1]);if(depth<1||depth>12)return 2;
 for(int x=0;x<256;x++)for(int e:{17,18,33,36,65,66,72,96,129,130,132,144,160,192})if((x&e)==e)truth[x]=true;
 for(int i=0;i<8;i++){Table tab{};for(int x=0;x<256;x++)if(x>>i&1)tab[x/64]|=U(1)<<(x%64);t.push_back(tab);for(int x=0;x<256;x++)if((x>>i&1)&&truth[x]&&!truth[x^(1<<i)])missing[0][i][x/64]|=U(1)<<(x%64);}
 gen(0);
}

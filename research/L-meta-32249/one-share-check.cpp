// Independent threshold checker. Price queries branch on the last AND or OR.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int A=16383, B=1023;
vector<unsigned char> mono(1<<24);
int ap,bn;
unordered_map<uint32_t,bool> memo;
int lowerPrice(int a,int b) {
    int x=a&~ap,y=b&bn;
    int zero=x?mono[x*1024+b]:0, one=y?mono[a*1024+y]:0;
    return min<int>(mono[a*1024+b],1+max(zero,one));
}
bool fits(int a,int b,int price) {
    if(mono[1024*a+b]<=price)return true;
    if(lowerPrice(a,b)>price)return false;
    if(!(a&~ap)&&!(b&bn))return true;
    if(price<2)return false;
    uint32_t key=((a*1024+b)<<5)+price;
    auto it=memo.find(key);if(it!=memo.end())return it->second;
    for(bool row:{false,true}){
        int side=row?a:b;
        for(int s=(side-1)&side;s>(side^s);s=(s-1)&side){
            int t=side^s,a1=row?s:a,b1=row?b:s,a2=row?t:a,b2=row?b:t;
            int min1=lowerPrice(a1,b1),max1=price-lowerPrice(a2,b2);
            for(int u=min1;u<=max1;++u)
                if(fits(a1,b1,u)&&fits(a2,b2,price-u))return memo[key]=true;
        }
    }
    return memo[key]=false;
}
int main(){
    ifstream in("mono.bin",ios::binary);assert(in.read((char*)mono.data(),mono.size()));
    vector<int> pos{9,17,18,33,36,40,65,66,68,80,129,132,136,160},neg{7,14,28,34,48,72,96,130,144,192};
    vector<int> costs(1<<24,100);vector<vector<int>> levels(9);
    for(int i=0;i<8;++i){int h=0;for(int j=0;j<14;++j)h|=((pos[j]>>i)&1)<<j;
        for(int j=0;j<10;++j)h|=((neg[j]>>i)&1)<<(14+j);
        costs[h]=0;levels[0].push_back(h);}
    for(int k=1;k<=8;++k)for(int l=0;l<k;++l){
        for(int x:levels[l])for(int y:levels[k-1-l])for(int h:{x|y,x&y})
            if(costs[h]>k){costs[h]=k;levels[k].push_back(h);}
    }
    for(auto const& row:levels)cout<<row.size()<<" ";cout<<endl;
    int remaining=0;
    for(int h=0;h<(1<<24);++h){
        ap=h&A;bn=h>>14;
        int pin=max(ap==A?0:mono[(A^ap)*1024+B],bn?mono[A*1024+bn]:0);
        int lower=mono[ap*1024+(B^bn)]-1;
        if(pin+lower>13)continue;
        assert(13-pin<=8);
        int k=costs[h];
        if(k==0||pin+k>13)continue;
        ++remaining;memo.clear();if(fits(A,B,15-k))cout<<"candidate "<<k<<" "<<h<<endl;
    }
    
    cout<<remaining<<" candidates checked; any passing table listed above\n";
}

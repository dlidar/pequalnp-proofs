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
constexpr int A=8191, B=63;
vector<unsigned char> mono(1<<19);
int ap,bn;
unordered_map<uint32_t,bool> memo;
int lowerPrice(int a,int b) {
    int x=a&~ap,y=b&bn;
    int zero=x?mono[x*64+b]:0, one=y?mono[a*64+y]:0;
    return min<int>(mono[a*64+b],1+max(zero,one));
}
bool fits(int a,int b,int price) {
    if(mono[64*a+b]<=price)return true;
    if(lowerPrice(a,b)>price)return false;
    if(!(a&~ap)&&!(b&bn))return true;
    if(price<2)return false;
    uint32_t key=((a*64+b)<<5)+price;
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
    vector<int> pos{17,33,34,36,65,66,80,96,130,132,136,144,192},neg{15,30,56,76,129,160};
    vector<int> costs(1<<19,100);vector<vector<int>> levels(8);
    for(int i=0;i<8;++i){int h=0;for(int j=0;j<13;++j)h|=((pos[j]>>i)&1)<<j;
        for(int j=0;j<6;++j)h|=((neg[j]>>i)&1)<<(13+j);
        costs[h]=0;levels[0].push_back(h);}
    for(int k=1;k<=7;++k)for(int l=0;l<k;++l){
        for(int x:levels[l])for(int y:levels[k-1-l])for(int h:{x|y,x&y})
            if(costs[h]>k){costs[h]=k;levels[k].push_back(h);}
    }
    int remaining=0;
    for(int h=0;h<(1<<19);++h){
        ap=h&A;bn=h>>13;
        int pin=max(ap==A?0:mono[(A^ap)*64+B],bn?mono[A*64+bn]:0);
        int lower=mono[ap*64+(B^bn)]-1;
        if(pin+lower>12)continue;
        assert(12-pin<=7);
        int k=costs[h];
        if(k==0||pin+k>12)continue;
        ++remaining;memo.clear();assert(!fits(A,B,14-k));
    }
    assert(remaining==551);
    cout<<remaining<<" decoder threshold queries excluded; minimum 14 gates with one shared output\n";
}

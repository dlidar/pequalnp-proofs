#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

// A ternary digit is zero if the variable is free, one or two if fixed to
// false or true. A free digit can be replaced by adding one or two powers
// of three, so descending index order is a topological ordering.
struct Cube { unsigned free, ones; bool leaf; };
int main() {
    std::array<unsigned,12> power{};
    unsigned count=1;
    for(auto &v:power){v=count;count*=3;}
    std::vector<Cube> cubes(count);
    for(unsigned state=0;state<count;++state){
        unsigned digits=state, free=0, ones=0;
        for(unsigned i=0;i<12;++i,digits/=3){
            unsigned d=digits%3;
            if(!d)free|=1u<<i;
            if(d==2)ones|=1u<<i;
        }
        bool leaf=false;
        for(unsigned i=0;i<4;++i)leaf |= ((free|ones)&(7u<<(3*i)))==0;
        for(unsigned j=0;j<3;++j)leaf |= std::popcount(ones&(585u<<j))>=2;
        cubes[state]={free,ones,leaf};
    }
    std::vector<std::array<uint16_t,2>> dp(count);
    unsigned mask;
    while(std::cin>>mask){
        for(unsigned state=count;state-- > 0;){
            auto [free,ones,leaf]=cubes[state];
            unsigned active=free&mask;
            unsigned value=std::popcount(ones&mask)%2;
            if(!active && !free){
                dp[state]={0,0}; dp[state][value]=1;continue;
            }
            for(unsigned parity=0;parity<2;++parity){
                if(!active && parity!=value){dp[state][parity]=0;continue;}
                if(leaf){dp[state][parity]=1;continue;}
                if(std::has_single_bit(active)){
                    unsigned i=std::countr_zero(active);
                    dp[state][parity]=dp[state+power[i]*(1+(parity^value))][parity];
                    continue;
                }
                unsigned best=65535;
                for(unsigned f=free;f;f&=f-1){
                    unsigned p=power[std::countr_zero(f)];
                    best=std::min(best,unsigned(dp[state+p][parity]+dp[state+2*p][parity]));
                }
                dp[state][parity]=best;
            }
        }
        std::cout<<mask<<" "<<dp[0][0]<<" "<<dp[0][1]<<std::endl;
    }
}

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>
using Mask = uint16_t;
constexpr Mask target = 5805;
struct Gate {Mask a,b,out;char op;};

int main() {
    std::array<Mask,8> raw{};
    for (int r=0;r<16;r++) { raw[r/4] |= 1u<<r; raw[4+r%4] |= 1u<<r; }
    std::vector<Gate> options;
    for (int i=0;i<8;i++) {
        options.push_back({raw[i],0,Mask(~raw[i]),'!'});
        for (int j=0;j<i;j++) {
            options.push_back({raw[i],raw[j],Mask(raw[i]&raw[j]),'&'});
            options.push_back({raw[i],raw[j],Mask(raw[i]|raw[j]),'|'});
        }
    }
    auto norm=[](const Gate& a,const Gate& b){return a.out<b.out;};
    std::stable_sort(options.begin(),options.end(),norm);
    options.erase(std::unique(options.begin(),options.end(),[](const Gate&a,const Gate&b){return a.out==b.out;}),options.end());
    for (auto gate:options) {
        std::vector<int8_t> cost(65536,-1); std::array<std::vector<Mask>,12> layers;
        auto add=[&](int k,Mask value){if(cost[value]<0){cost[value]=k;layers[k].push_back(value);}};
        for(auto value:raw)add(0,value);
        add(0,gate.out);
        for (int k=1;k<=10 && cost[target]<0;k++) {
            for(auto a:layers[k-1])add(k,Mask(~a));
            for(int i=0;i<=k-1-i;i++)for(auto a:layers[i])for(auto b:layers[k-1-i]) {
                add(k,Mask(a&b));add(k,Mask(a|b));
            }
        }
        std::cout<<gate.out<<' '<<gate.op<<' '<<gate.a<<' '<<gate.b<<' '<<int(cost[target])<<'\n';
    }
}

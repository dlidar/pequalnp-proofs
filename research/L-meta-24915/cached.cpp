#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Mask = unsigned;
constexpr unsigned domain = (1u << 21) - 1;
struct Node { Mask a=0,b=0; char op=0; };

int main() {
    std::array<Mask,6> raw{};
    Mask target = 0;
    int bit = 0;
    for (int i=0;i<6;++i) for (int j=i;j<6;++j,++bit) {
        raw[i] |= 1u<<bit;
        raw[j] |= 1u<<bit;
        if ((4294973ULL >> (6*i+j)) & 1) target |= 1u<<bit;
    }
    std::vector<std::pair<std::string,Mask>> signals;
    for (int i=0;i<6;++i) {
        signals.emplace_back("!"+std::to_string(i),domain^raw[i]);
        for (int j=0;j<i;++j) {
            signals.emplace_back(std::to_string(j)+"&"+std::to_string(i),raw[i]&raw[j]);
            signals.emplace_back(std::to_string(j)+"|"+std::to_string(i),raw[i]|raw[j]);
        }
    }
    for (const auto& [name,value]:signals) {
        std::array<std::vector<Mask>,11> layers;
        std::vector<Node> source(domain+1);
        auto add=[&](int d,Mask x,Node node){
            if (source[x].op) return;
            layers[d].push_back(x);
            source[x]=node;
        };
        for(unsigned j=0;j<6;++j) add(0,raw[j],{j,0,'x'});
        add(0,value,{6,0,'x'});
        for(int d=1;d<=10;++d){
            for(Mask a:layers[d-1]) add(d,domain^a,{a,0,'!'});
            for(int i=0;i<=d-1-i;++i)
                for(Mask a:layers[i]) for(Mask b:layers[d-1-i]) {
                    add(d,a|b,{a,b,'|'}); add(d,a&b,{a,b,'&'});
                }
            if(source[target].op) {
                auto expression=[&](auto&& self,Mask x)->std::string{
                    Node z=source[x];
                    if(z.op=='x') return z.a==6?"H":std::to_string(z.a);
                    if(z.op=='!') return "(!"+self(self,z.a)+")";
                    return "("+self(self,z.a)+z.op+self(self,z.b)+")";
                };
                std::cout<<name<<" "<<d<<" "<<expression(expression,target)<<std::endl;
                break;
            }
        }
    }
}

// Check every promised input to the generated n=1 circuit, including all junk and ordinal bits.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using U = std::uint64_t;
struct Gate { int op,a,b; };
int main(){
    int ng; std::cin >> ng;
    std::vector<Gate> gates(ng);
    for(int j=0;j<ng;++j){
        auto& g=gates[j];std::cin>>g.op>>g.a>>g.b;
        assert(g.op>=0 && g.op<=2 && g.a>=0 && g.a<29+j && g.b>=0 && g.b<29+j);
    }
    std::array<int,13> out;
    for(int& a:out){std::cin>>a;assert(a>=0 && a<29+ng);}
    // All 9 pins, indexed by the base-three key. Compute histograms from all 4 spins.
    std::array<int,9> target{};
    for(int p=0;p<9;++p){
        int d0=p%3,d1=p/3;
        for(int a=0;a<=1;++a)for(int b=0;b<=1;++b){
            if((d0 && d0!=1+a)||(d1 && d1!=1+b))continue;
            target[p]+=1 << ((a!=b)?9:0);
        }
    }
    // Eight permission bits would be redundant: there are six, arranged by digit then side.
    // Evaluating 64 permission masks in parallel leaves 2^20 remaining raw tuples.
    std::array<U,6> permissions{};
    for(int k=0;k<6;++k)for(int lane=0;lane<64;++lane)
        permissions[k]|=U((lane>>k)&1)<<lane;
    std::array<U,9> permitted;
    for(int p=0;p<9;++p)permitted[p]=permissions[2*(p%3)] & permissions[2*(p/3)+1];
    std::vector<U> wires(29+ng);
    wires[0]=0;wires[1]=wires[2]=~U(0);
    for(int i=0;i<6;++i)wires[3+i]=permissions[i];
    for(int h=0;h<4096;++h){
        std::array<U,4> count_bits{};
        std::array<std::array<U,4>,9> rank_bits{};
        std::array<std::array<U,4>,16> picked{}; // present/value pairs at each vertex
        std::array<U,16> in_range{};
        std::array<U,9> in_fiber{};
        for(int lane=0;lane<64;++lane){
            U flag=U(1)<<lane;
            int ordinal=0;
            for(int p=0;p<9;++p)if(h==target[p] && (permitted[p]&flag)){
                in_fiber[p]|=flag;in_range[ordinal]|=flag;
                for(int k=0;k<4;++k)if(ordinal&(1<<k))rank_bits[p][k]|=flag;
                int a=p%3,b=p/3;
                for(int j=0;j<4;++j)
                    if((j==0 && a)||(j==1 && a==2)||(j==2 && b)||(j==3 && b==2))picked[ordinal][j]|=flag;
                ++ordinal;
            }
            for(int k=0;k<4;++k)if(ordinal&(1<<k))count_bits[k]|=flag;
        }
        for(int k=0;k<12;++k)wires[9+k]=U(0)-((h>>k)&1);
        for(int tail=0;tail<256;++tail){
            for(int k=0;k<8;++k)wires[21+k]=U(0)-((tail>>k)&1);
            for(int j=0;j<ng;++j){
                auto g=gates[j];auto a=wires[g.a],b=wires[g.b];
                wires[29+j]=g.op==0?(a&b):g.op==1?(a|b):~a;
            }
            int a=(tail&1)?1+((tail>>2)&1):0,b=(tail&2)?1+((tail>>3)&1):0;
            int p=a+3*b,z=tail>>4;
            for(int k=0;k<4;++k){
                assert(wires[out[k]]==count_bits[k]);
                assert(((wires[out[4+k]]^rank_bits[p][k])&in_fiber[p])==0);
                U mask=in_range[z];
                if(k%2)mask&=picked[z][k-1];
                assert(((wires[out[9+k]]^picked[z][k])&mask)==0);
            }
            assert(wires[out[8]]==in_fiber[p]);
        }
    }
    std::cout << ng << " gates, all 67108864 promised bit vectors passed\n";
}

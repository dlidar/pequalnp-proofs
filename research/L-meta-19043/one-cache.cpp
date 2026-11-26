#include <array>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>

using Mask = std::uint16_t;
constexpr Mask target = 5805;
constexpr int budget = 9;
using Layers = std::array<std::vector<Mask>,budget+1>;

Layers formulas(std::vector<Mask> inputs, int limit) {
    Layers layers;
    std::vector<bool> seen(65536);
    auto add = [&](int cost, Mask mask) {
        if (!seen[mask]) {
            seen[mask] = true;
            layers[cost].push_back(mask);
        }
    };
    for (Mask m : inputs) add(0,m);
    for (int k = 1; k <= limit; ++k) {
        for (Mask a : layers[k-1]) add(k,Mask(~a));
        for (int i = 0; i <= k-1-i; ++i) {
            for (Mask a : layers[i]) for (Mask b : layers[k-1-i]) {
                add(k,Mask(a|b));
                add(k,Mask(a&b));
            }
        }
    }
    return layers;
}

int main() {
    std::vector<Mask> raw(8);
    for (int cell = 0; cell < 16; ++cell) {
        raw[cell/4] |= 1u<<cell;
        raw[4+cell%4] |= 1u<<cell;
    }
    auto prefixes = formulas(raw,budget);
    for (int c = 0; c <= budget; ++c) {
        int hits = 0;
        for (Mask h : prefixes[c]) {
            auto extended = raw;
            extended.push_back(h);
            auto decoders = formulas(extended,budget-c);
            for (int k = 0; k <= budget-c; ++k) {
                if (std::find(decoders[k].begin(),decoders[k].end(),target) != decoders[k].end()) {
                    std::cout << "witness " << h << ' ' << c << ' ' << k <<std::endl;
                    ++hits;
                    break;
                }
            }
        }
        std::cout << c << ' ' << prefixes[c].size() << ' ' << hits << std::endl;
    }
}

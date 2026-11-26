// Independently find each extremal test by visiting the whole Boolean cube.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
int main() {
    constexpr unsigned n = 1u << 24, left = 11, right = (1u << 15) | (1u << 16) | (1u << 18);
    std::array<unsigned, 12> neighbours{};
    std::array<std::vector<unsigned>, 12> lines;
    for (unsigned i = 0; i < 12; ++i) for (unsigned j = 0; j < 12; ++j) {
        unsigned s = (i + (i >= 9) + j + 1) % 13;
        if (s == 0 || s == 1 || s == 3 || s == 9) {
            neighbours[i] |= 1u << j;
            lines[i].push_back(12+j);
        }
    }
    std::vector<std::uint8_t> positive(n), negative(n);
    for (unsigned x=0; x<n; ++x) {
        bool edge = false;
        for (unsigned i=0; i<12; ++i)
            if ((x & (1u<<i)) && ((x>>12) & neighbours[i])) { edge=true; break; }
        positive[x] = (edge?1:0) | ((!edge && (x&left))?2:0) | ((!edge && (x&right))?4:0);
        negative[x] = edge ? 0 : (1 | ((x&left)?0:2) | ((x&right)?0:4));
    }
    std::array<unsigned,3> p{},q{};
    unsigned rows=0;
    for (unsigned x=0; x<n; ++x) {
        unsigned a=positive[x], b=negative[x];
        for(unsigned i=0; i<24 && (a||b); ++i) {
            unsigned z=1u<<i;
            if (x&z) a &= ~positive[x^z];
            else b &= ~negative[x^z];
        }
        for(unsigned i=0; i<3; ++i) {p[i]+=(a>>i)&1;q[i]+=(b>>i)&1;}
        rows+=!!(a|b);
    }
    std::cout << "Minimal positives " << p[0] << " " << p[1] << " " << p[2]
              << "; maximal negatives " << q[0] << " " << q[1] << " " << q[2]
              << "; union " << rows << "\n";
    assert((p==std::array<unsigned,3>{45,3,3}));
    assert((q==std::array<unsigned,3>{420,197,197}) && rows==737);
}

// Exact chain decrease count for the desk's n=5, w=1, q=3 example.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <iostream>
#include <vector>
int main() {
    constexpr int n = 5, cells = 20, rank = 3, count = 1 << cells;
    std::array<unsigned, cells> forbidden{};
    for (int z = 0; z < 32; ++z) {
        for (int i = 0; i < n; ++i) {
            auto bit = [&](int t) { return (z >> (n - 1 - t % n)) & 1; };
            forbidden[4*i + bit(i) + 2*bit(i+1)] |= 1u << z;
        }
    }
    // Each mask names the disabled table entries. Removing entries shrinks the solution set.
    std::vector<unsigned> sols(count, ~0u);
    std::vector<int> word(count, -1), depth(count, -1), parent(count, -1);
    for (int m = 0; m < count; ++m) {
        if (m) sols[m] = sols[m & (m-1)] & ~forbidden[std::countr_zero(unsigned(m))];
        if (std::popcount(sols[m]) <= rank) continue;
        unsigned left = sols[m];
        for (int j = 0; j < rank; ++j) left &= left-1;
        word[m] = std::countr_zero(left);
        depth[m] = 0;
        for (int a = m; a; a &= a-1) {
            int p = m ^ (a & -a);
            assert(word[p] >= 0 && word[p] <= word[m]);
            int score = depth[p] + (word[m] != word[p]);
            if (score > depth[m]) { depth[m] = score; parent[m] = p; }
        }
    }
    int end = std::max_element(depth.begin(), depth.end()) - depth.begin();
    std::cout << "greatest strict decreases on an increasing valid chain: " << depth[end] << '\n';
    std::cout << "disabled-mask ranked-word\n";
    for (int m = end; m >= 0; m = parent[m]) std::cout << m << ' ' << word[m] << '\n';
}

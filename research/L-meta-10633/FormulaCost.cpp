// Compute the minimum number of binary monotone formula gates for L-meta-10633.
// Each nonempty subproblem separates some edges from some maximal independent sets.
// The two partitions are justified by BinaryFormulaPanels.exact_cost.
#include <algorithm>
#include <array>
#include <iostream>

constexpr std::array edges{9, 10, 17, 20, 33, 34, 40, 48, 66, 68, 72, 80, 96};
constexpr std::array negatives{7, 12, 18, 24, 36, 65};
constexpr int numPositiveSets = 1 << edges.size();
constexpr int numNegativeSets = 1 << negatives.size();
static int cost[numPositiveSets][numNegativeSets];

template <std::size_t N>
int matchingRows(const std::array<int, N>& rows, int bit, bool expected) {
    int selected = 0;
    for (std::size_t i = 0; i < N; ++i)
        if (bool(rows[i] & (1 << bit)) == expected) selected |= 1 << i;
    return selected;
}

int main() {
    std::array<int, 7> positiveBits, negativeBits;
    for (int bit = 0; bit < 7; ++bit) {
        positiveBits[bit] = matchingRows(edges, bit, true);
        negativeBits[bit] = matchingRows(negatives, bit, false);
    }
    for (int p = 1; p < numPositiveSets; ++p) {
        for (int n = 1; n < numNegativeSets; ++n) {
            int best = 10000;
            for (int bit = 0; bit < 7; ++bit)
                if (!(p & ~positiveBits[bit]) && !(n & ~negativeBits[bit])) best = 0;
            if (best) {
                // In a minimum formula both sides of the split are nonempty.
                // An empty side lets the other child separate the whole panel.
                for (int a = (p-1) & p; a > (p ^ a); a = (a-1) & p)
                    best = std::min(best, 1 + cost[a][n] + cost[p ^ a][n]);
                for (int a = (n-1) & n; a > (n ^ a); a = (a-1) & n)
                    best = std::min(best, 1 + cost[p][a] + cost[p][n ^ a]);
            }
            cost[p][n] = best;
        }
    }
    std::cout << "minimum formula gates: " << cost[numPositiveSets-1][numNegativeSets-1] << '\n';
}

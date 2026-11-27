#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

struct Node {
    int first = -1;
    int second = -1;
    char op = 0;
};
constexpr int target = 114591;
constexpr int full = 1048575;

void search(bool allow_not) {
    std::vector<Node> nodes(1 << 20);
    std::array<std::vector<int>, 20> layer;
    auto add = [&](int cost, int mask, Node node) {
        if (nodes[mask].op) return;
        nodes[mask] = node;
        layer[cost].push_back(mask);
    };
    for (int k = 0; k < 9; ++k) {
        int mask = 0;
        for (int r = 0; r < 20; ++r)
            if (r/5 == k || 4+r%5 == k) mask |= 1 << r;
        add(0, mask, {k,-1,'x'});
    }
    for (int n = 1; n < 20; ++n) {
        if (allow_not) for (int a : layer[n-1]) add(n, full ^ a, {a,-1,'!'});
        for (int i = 0; i <= n-1-i; ++i)
            for (int a : layer[i])
                for (int b : layer[n-1-i]) {
                    add(n, a | b, {a,b,'|'});
                    add(n, a & b, {a,b,'&'});
                }
        if (nodes[target].op) {
            auto display = [&](auto&& self, int v) -> std::string {
                Node t = nodes[v];
                if (t.op == 'x') return std::to_string(t.first);
                if (t.op == '!') return "(!"+self(self,t.first)+")";
                return "("+self(self,t.first)+t.op+self(self,t.second)+")";
            };
            std::cout << (allow_not ? "Unrestricted" : "Monotone") << " formula " << n << " " << display(display,target) << "\n";
            return;
        }
    }
}
int main() { search(false); search(true); }

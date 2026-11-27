#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using Row = std::array<int,8>;

int add(int x, int y, int q) {
    return (q == 4 || q == 8) ? (x ^ y) : (x+y)%q;
}
int sub(int x, int y, int q) {
    return (q == 4 || q == 8) ? (x ^ y) : (x+q-y)%q;
}
int parity(const Row &f, int q) {
    int odd = 0;
    for (int i=0; i<q; ++i)
        for (int j=0; j<i; ++j)
            odd ^= f[j] > f[i];
    return odd;
}
void classify(int q) {
    // Constants let us normalize P(0)=0. The vanishing sum determines P(q-1).
    int space = 1;
    for (int i=0; i<q-2; ++i) space *= q;
    std::vector<int> witnesses(space,0);
    Row cycle{}, labels{}, successor{};
    std::iota(cycle.begin(),cycle.end(),0);
    do {
        for (int i=0; i<q; ++i) successor[cycle[i]] = cycle[(i+1)%q];
        // At the vertex 0, P(0)+successor(0) must be successor(0).
        labels[0] = successor[0];
        int pos = 1;
        for (int x=0; x<q; ++x) if (x!=labels[0]) labels[pos++] = x;
        do {
            int code = 0;
            for (int i=q-2; i>=1; --i) code = q*code+sub(labels[i],successor[i],q);
            ++witnesses[code];
        } while (std::next_permutation(labels.begin()+1,labels.begin()+q));
    } while (std::next_permutation(cycle.begin()+1,cycle.begin()+q));
    int insoluble = 0;
    std::array<int,9> bins{};
    std::array<int,2> perm_bad{};
    for (int code=0; code<space; ++code) {
        if (witnesses[code]) continue;
        Row f{};
        int c = code, sum = 0, colors = 1;
        for (int i=1; i<q-1; ++i) {
            f[i] = c%q; c /= q;
            sum = add(sum,f[i],q);
            colors |= 1 << f[i];
        }
        f[q-1] = sub(0,sum,q);
        colors |= 1 << f[q-1];
        int image_size=0;
        for (int i=0; i<q; ++i) image_size += (colors>>i)&1;
        ++bins[image_size];
        if (image_size==q) ++perm_bad[parity(f,q)];
        ++insoluble;
    }
    std::cout << "q=" << q << " normalized tables=" << space << " insoluble=" << insoluble
              << " image-size counts:";
    for (int i=1; i<=q; ++i) if (bins[i]) std::cout << ' ' << i << '=' << bins[i];
    std::cout << " bad permutations (even,odd)=" << perm_bad[0] << ',' << perm_bad[1] << '\n';
}
int main() { for (int q : {3,4,5,7,8}) classify(q); }

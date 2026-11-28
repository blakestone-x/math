// Input: sorted exponent triples from three_prime_profiles.py.
// Argument: where to write the surviving intervals of the smallest base.
#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using U64 = std::uint64_t;
using U128 = __uint128_t;
using I64 = std::int64_t;
using Triple = std::array<int,3>;
using Bounds = std::array<I64,3>;
constexpr I64 scale = 32;
std::array<int,257> log_table{};

int bit_length(U128 x) {
    U64 high = x >> 64;
    return high ? 64 + std::bit_width(high) : std::bit_width(static_cast<U64>(x));
}

// Both endpoints enclose 32 log_2(x). The top 8 bits suffice.
I64 log_lower(U128 x) {
    if (x < 128) return log_table[static_cast<unsigned>(x)];
    int shift = bit_length(x)-8;
    return scale*shift + log_table[static_cast<unsigned>(x >> shift)];
}
I64 log_upper(U128 x) {
    if (x < 128) return 1 + log_table[static_cast<unsigned>(x)];
    int shift = bit_length(x)-8;
    return scale*shift + 1 + log_table[1+static_cast<unsigned>(x >> shift)];
}
I64 ceil_div(I64 a, I64 b) { return (a+b-1)/b; }

bool inconsistent(const Triple& e, I64 log_d_plus_one, Bounds low, Bounds high) {
    // Every inequality update is valid independently. Extra rounds would only
    // tighten these intervals, so three rounds already give a rigorous test.
    for (int pass = 0; pass != 3; ++pass) {
        for (int t=1; t<3; ++t) low[t] = std::max(low[t], low[t-1]);
        for (int t=1; t>=0; --t) high[t] = std::min(high[t], high[t+1]);
        for (int t=0; t<3; ++t) if (low[t] > high[t]) return true;
        for (unsigned subset : {1,2,4,3,5,6,7}) {
            Triple weight{};
            I64 upper_sum = log_d_plus_one + log_upper(std::popcount(subset));
            for (int t=0; t<3; ++t) {
                weight[t] = (subset >> t & 1) ? 2 : e[t];
                upper_sum += weight[t]*high[t];
            }
            int witnesses=0, index=-1;
            for (int t=0; t<3; ++t) {
                if ((subset >> t & 1) && e[t]*low[t] <= upper_sum - weight[t]*high[t]) {
                    ++witnesses;
                    index=t;
                }
            }
            if (witnesses == 0) return true;
            if (witnesses != 1) continue;
            I64 rhs = upper_sum - weight[index]*high[index];
            high[index] = std::min(high[index], ceil_div(rhs, e[index]));
            for (int t=0; t<3; ++t) if (t != index) {
                I64 lower = e[index]*low[index] - rhs + weight[t]*high[t];
                if (lower>0) low[t] = std::max(low[t], lower/weight[t]);
            }
        }
    }
    return false;
}

U128 threshold_floor(U64 x, U64 i, U64 K) {
    U64 D = (i+1)*K;
    U128 denominator = static_cast<U128>(x-1-i*K)*(x-1)+K;
    return static_cast<U128>(D+1)*(x-1)*(x-1)/denominator;
}

bool empty_interval(const Triple& e, U64 left, U64 right) {
    U64 i=e[0], j=e[1], k=e[2], K=(j+1)*(k+1), D=(i+1)*K;
    U128 t_min=threshold_floor(right,i,K), t_max=threshold_floor(left,i,K);
    U128 y_min = std::max<U128>(std::max(left+1, j*(D/(j+1))+1), j*(t_min-1)/(j+1)+1);
    U128 y_max = 2*t_max+5;
    if (y_min > y_max) return true;
    I64 xl=log_lower(left), xu=log_upper(right), yl=log_lower(y_min), yu=log_upper(y_max);
    I64 ld=log_upper(D+1);
    // z^k divides H_i(x)H_j(y), which is at most (D+1)x^i y^j.
    I64 zu=ceil_div(ld+e[0]*xu+e[1]*yu,e[2]);
    for (unsigned subset : {1,2,3}) {
        int dx=(subset & 1) ? 2 : e[0];
        int dy=(subset & 2) ? 2 : e[1];
        bool x_small_error = !(subset & 1) || e[0]*xl >= ld + 2*scale + dy*yu;
        bool y_small_error = !(subset & 2) || e[1]*yl >= ld + 2*scale + dx*xu;
        if (x_small_error && y_small_error) zu=std::min(zu,ld+2*scale+dx*xu+dy*yu);
    }
    return inconsistent(e,ld,{xl,yl,yl},{xu,yu,zu});
}

mpz_class power(const mpz_class& x, unsigned e) {
    mpz_class n;
    mpz_pow_ui(n.get_mpz_t(), x.get_mpz_t(), e);
    return n;
}
mpz_class moment(const mpz_class& x, unsigned e, const mpz_class& xpow) {
    return (((e+1)*x-e-2)*x*xpow+1)/((x-1)*(x-1));
}
std::vector<unsigned> prime_list(unsigned bound) {
    std::vector<bool> prime(bound+1,true);
    std::vector<unsigned> list;
    for (unsigned p=2; p<=bound; ++p) if (prime[p]) {
        list.push_back(p);
        if (p<=bound/p) for (unsigned m=p*p; m<=bound; m+=p) prime[m]=false;
    }
    return list;
}
struct Job { Triple e; unsigned x, y_max; };
struct Count { U64 input=0, orders=0, remaining=0, intervals=0, jobs=0, pairs=0, last=0; };

int main(int argc,char** argv) {
    if (argc != 2) throw std::runtime_error("Supply an output path for the interval certificate.");
    std::ofstream boxes(argv[1]);
    if (!boxes) throw std::runtime_error("Cannot write the interval certificate.");
    for (unsigned t=1; t<=256; ++t) {
        mpz_class value;
        mpz_ui_pow_ui(value.get_mpz_t(),t,scale);
        log_table[t]=mpz_sizeinbase(value.get_mpz_t(),2)-1;
    }
    std::vector<Job> jobs;
    std::map<int,Count> totals;
    unsigned last_bound=2;
    Triple input;
    while (std::cin >> input[0] >> input[1] >> input[2]) {
        int c=input[2], b=input[1], a=input[0];
        if (!(a>=b && b>=c && (c==4||c==6||c==8||c==9) && b<=10*c+7 && a<=(3*c+4)*b+3*c))
            throw std::runtime_error("Exponent profile out of range.");
        auto &counts=totals[c]; ++counts.input;
        Triple e=input; std::sort(e.begin(),e.end());
        do {
            ++counts.orders;
            U64 i=e[0], j=e[1], k=e[2], K=(j+1)*(k+1), D=(i+1)*K;
            U64 first=i*K+1, last=3*(D+1)+1;
            bool remaining=false;
            for (U64 l=first; l<=last;) {
                U64 u=std::min(last,first+2*(l-first));
                if (!empty_interval(e,l,u)) {
                    ++counts.intervals; remaining=true;
                    boxes<<i<<' '<<j<<' '<<k<<' '<<l<<' '<<u<<'\n';
                    for (U64 x=l; x<=u; ++x) {
                        bool prime=true;
                        for (U64 v=2; v<=x/v; ++v) if (x%v==0) { prime=false; break; }
                        if (!prime) continue;
                        U128 bound=2*threshold_floor(x,i,K)+5;
                        if (bound>100000000) throw std::runtime_error("Middle-base sieve needs enlargement.");
                        jobs.push_back({e,static_cast<unsigned>(x),static_cast<unsigned>(bound)});
                        ++counts.jobs; last_bound=std::max(last_bound,static_cast<unsigned>(bound));
                    }
                }
                l=u+1;
            }
            if (remaining) ++counts.remaining;
        } while (std::next_permutation(e.begin(),e.end()));
    }
    boxes.close();
    if (!boxes || !std::cin.eof() || totals.size()!=4) throw std::runtime_error("Incomplete input or certificate.");
    constexpr std::array<unsigned,4> expected={502,324,5849,13779};
    unsigned order=0;
    for (auto& [c,n]:totals) if (n.input!=expected[order++]) throw std::runtime_error("Wrong input count.");
    auto primes=prime_list(last_bound);
    for (const auto &job:jobs) {
        auto [i,j,k]=job.e;
        unsigned x=job.x, D=(i+1)*(j+1)*(k+1);
        auto& n=totals[std::min({i,j,k})];
        mpz_class X=power(x,i), A=moment(x,i,X), base=(D+1)*X, g=base-(j+1)*(k+1)*A;
        if (g<=0) continue;
        mpz_class first=j*(k+1)*A/g;
        unsigned low=std::max(x,j*(D/(j+1)));
        if (first>job.y_max) continue;
        low=std::max(low,static_cast<unsigned>(first.get_ui()));
        if (low>=job.y_max) continue;
        auto end=std::upper_bound(primes.begin(),primes.end(),job.y_max);
        for (auto it=std::upper_bound(primes.begin(),primes.end(),low); it!=end; ++it) {
            unsigned y=*it; ++n.pairs;
            mpz_class Y=power(y,j), W=A*moment(y,j,Y), M=base*Y, G=M-(k+1)*W;
            if (G<=0) continue;
            mpz_class z=(k*W+G-1)/G;
            if (z<=std::max<unsigned>(y,k*(D/(k+1))) || mpz_even_p(z.get_mpz_t())) continue;
            ++n.last;
            mpz_class Z=power(z,k);
            if (W*moment(z,k,Z)==M*Z) throw std::runtime_error("An integer equality was found.");
        }
    }
    std::cout<<"least profiles orders surviving_orders intervals smallest_primes middle_primes last_candidates\n";
    for (const auto& [c,n]:totals) std::cout<<c<<' '<<n.input<<' '<<n.orders<<' '<<n.remaining<<' '<<n.intervals<<' '<<n.jobs<<' '<<n.pairs<<' '<<n.last<<'\n';
    std::cout<<"Largest middle-prime sieve bound: "<<last_bound<<"\nFull equalities: 0\n";
}

// Exhaust arbitrary prime bases and all powers of two for the indicated odd exponents.
#include <gmpxx.h>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using U64=std::uint64_t;
struct Local { mpz_class power, moment, sigma; };
Local prime_power(unsigned p, unsigned e) {
    Local v{1,1,1};
    for (unsigned i=1;i<=e;++i) { v.power*=p; v.moment+=(i+1)*v.power; v.sigma+=v.power; }
    return v;
}
struct Residues {
    unsigned m, period;
    std::vector<unsigned long> allowed;
};
// Return (F_e(p),G_e(p)) for local sums normalized by p^e.
std::pair<int,int> local_mod(int e,int p,int m) {
    int inv=1; while (p*inv%m!=1) ++inv;
    int F=1,G=1;
    for (int t=1;t<=e;++t) { F=(t+1+inv*F)%m; G=(1+inv*G)%m; }
    return {F,G};
}
std::vector<Residues> filters(unsigned b,unsigned c,unsigned D) {
    std::vector<Residues> result;
    for (unsigned m:{3,5,7,11,13,17,19}) {
        unsigned order=1, half=(m+1)/2, t=half;
        while (t!=1) { t=t*half%m; ++order; }
        unsigned period=m*order;
        Residues row{m,period,std::vector<unsigned long>(period)};
        std::vector<std::pair<int,int>> first(m),last(m);
        for (unsigned r=1;r<m;++r) { first[r]=local_mod(b,r,m); last[r]=local_mod(c,r,m); }
        unsigned inv2a=1;
        for (unsigned a=0;a<period;++a) {
            int h=(2*a+inv2a)%m, s=(2+m-inv2a)%m, target=2*(a+1)*D%m;
            for (unsigned r=1;r<m;++r) for (unsigned v=1;v<m;++v) {
                if ((h*first[r].first*last[v].first+s*first[r].second*last[v].second)%m==target) {
                    row.allowed[a]|=1UL<<r; break;
                }
            }
            inv2a=inv2a*half%m;
        }
        result.push_back(std::move(row));
    }
    return result;
}
int main(int argc,char**argv) {
    unsigned cap=argc>1?std::stoul(argv[1]):256;
    if (cap<4 || cap>2048) throw std::runtime_error("Use a divisor-count cap from 4 through 2048.");
    std::vector<unsigned> primes;
    unsigned limit=160*cap+1;
    std::vector<bool> sieve(limit+1,true);
    for (unsigned p=2;p<=limit;++p) if (sieve[p]) {
        if (p!=2) primes.push_back(p);
        if (p<=limit/p) for (unsigned t=p*p;t<=limit;t+=p) sieve[t]=false;
    }
    U64 pairs=0, parity=0, choices=0, exact=0, candidates=0;
    for (unsigned b=1;2*(b+1)<=cap;++b) for (unsigned c=1;(b+1)*(c+1)<=cap;++c) {
        ++pairs;
        bool square=(b%2==0&&c%2==0), odd_H=(b%4<=1&&c%4<=1);
        if (square!=odd_H) { ++parity; continue; }
        unsigned D=(b+1)*(c+1); auto mods=filters(b,c,D);
        std::vector<Local> first;
        for (unsigned p:primes) {
            if (p>160*D+1) break;
            first.push_back(prime_power(p,b));
        }
        for (unsigned a=0;a+1<32*D;++a) {
            mpz_class two=mpz_class(1)<<(a+1), H2=a*two+1, S2=two-1;
            auto stop=std::upper_bound(primes.begin(),primes.end(),5*(a+1)+1);
            for (auto it=std::upper_bound(primes.begin(),primes.end(),a/2);it!=stop;++it) {
                unsigned p=*it; ++choices; bool possible=true;
                for (const auto& f:mods) if (p>f.m && !(f.allowed[a%f.period]>>(p%f.m)&1)) { possible=false; break; }
                if (!possible) continue;
                ++exact; const auto& P=first[it-primes.begin()];
                mpz_class U=H2*P.moment, V=S2*P.sigma;
                mpz_class M=two*(a+1)*D*P.power, gap=M-(c+1)*U-V;
                if (gap<=0) continue;
                mpz_class q=(c*U+V+gap-1)/gap;
                if (q<=p || mpz_even_p(q.get_mpz_t())) continue;
                ++candidates;
                // Necessary dyadic divisibility, bounded using only binary lengths.
                // H(p^b q^c) <= D*(3/2)^2 * p^b q^c.
                if ((a+1)>mpz_sizeinbase(P.moment.get_mpz_t(),2)+c*mpz_sizeinbase(q.get_mpz_t(),2)+c+1) continue;
                mpz_class qpow; mpz_pow_ui(qpow.get_mpz_t(),q.get_mpz_t(),c);
                mpz_class Hq=(((c+1)*q-(c+2))*q*qpow+1)/((q-1)*(q-1));
                mpz_class Sq=(q*qpow-1)/(q-1);
                if (U*Hq+V*Sq==M*qpow) {
                    std::cerr<<"Equality: "<<a<<' '<<p<<' '<<b<<' '<<q<<' '<<c<<'\n';
                    return 1;
                }
            }
        }
    }
    std::cout<<"Odd divisor-count bound: "<<cap<<"\nOrdered odd exponent pairs: "<<pairs
             <<"\nExcluded by parity: "<<parity<<"\nDyadic exponent and smallest-prime choices: "<<choices
             <<"\nAfter unit-residue tests: "<<exact<<"\nOrdered odd last-base candidates: "<<candidates
             <<"\nEqualities: 0\n";
}

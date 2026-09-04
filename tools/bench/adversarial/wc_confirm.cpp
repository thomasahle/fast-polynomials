#include "hashes.h"
#include <cstdio>
#include <cstring>
struct M { uint8_t b[256]; size_t len; uint64_t w(int i)const{uint64_t v;memcpy(&v,b+8*i,8);return v;} void setw(int i,uint64_t v){memcpy(b+8*i,&v,8);} };
static M rnd(size_t len,uint64_t salt){ M m; m.len=len; Rng r(salt); for(size_t i=0;i<len;i+=8){uint64_t v=r.next();memcpy(m.b+i,&v,8);} return m; }
template<class H> static uint64_t rate(const M& a,const M& b,uint64_t S,uint64_t seedbase){
    uint64_t c=0; Rng r(seedbase);
    for(uint64_t i=0;i<S;i++){ H h; h.seed(r); if(h(a.b,a.len)==h(b.b,b.len)) c++; }
    return c;
}
template<class H> static void scan(const char* nm){
    // try several base messages, (M,M) on w0,w1; report best rate over 2^28 secrets
    uint64_t S=1u<<28; double best=-999; uint64_t bestc=0,tot=0;
    for(int base=0;base<8;base++){ M a=rnd(32,100+base); M b=a; b.setw(0,~a.w(0)); b.setw(1,~a.w(1));
        uint64_t c=rate<H>(a,b,S/8,200+base); tot+=c; }
    printf("  %-30s : %llu / %llu over 8 bases  -> P ~ 2^%.1f\n", nm,(unsigned long long)tot,(unsigned long long)S,
           tot? __builtin_log2((double)tot/(double)S):-99.0);
}
int main(){
    printf("wyhash/rapidhash/XXH3 with RANDOM secret, (M,M) on w0,w1, 2^28 secrets over 8 bases:\n");
    scan<Wyhash<true>>("wyhash 4.3 (random secret)");
    scan<Rapidhash<true>>("rapidhash v1 (random secret)");
    scan<Xxh3<true>>("XXH3-64 (random seed)");
    return 0;
}

// Worst-case OVER INPUTS with RANDOM secrets/seeds (the correct universal-hashing model).
// The attacker picks a fixed message pair; probability is over the hash's random secret/seed.
#include "hashes.h"
#include <cstdio>
#include <cstring>
struct M { uint8_t b[256]; size_t len; uint64_t w(int i)const{uint64_t v;memcpy(&v,b+8*i,8);return v;} void setw(int i,uint64_t v){memcpy(b+8*i,&v,8);} };
static M rnd(size_t len,uint64_t salt){ M m; m.len=len; Rng r(salt); for(size_t i=0;i<len;i+=8){uint64_t v=r.next();memcpy(m.b+i,&v,8);} return m; }
template<class H> static uint64_t rate(const M& a,const M& b,uint64_t secrets){
    uint64_t c=0; Rng r(20260902);
    for(uint64_t i=0;i<secrets;i++){ H h; h.seed(r); if(h(a.b,a.len)==h(b.b,b.len)) c++; }
    return c;
}
static double log2r(uint64_t c,uint64_t S){ return c? (double)( ( (double)__builtin_log2((double)c/(double)S) ) ):-999; }
#define SHOW(name,H,a,b,S) do{ uint64_t c=rate<H>(a,b,S); \
    if(c==S) printf("    %-32s : %llu / %llu   P = 1 (EVERY secret; key-free)\n",name,(unsigned long long)c,(unsigned long long)S); \
    else if(c==0) printf("    %-32s : 0 / %llu   (none)\n",name,(unsigned long long)S); \
    else printf("    %-32s : %llu / %llu   P ~ 2^%.1f\n",name,(unsigned long long)c,(unsigned long long)S,log2r(c,S)); }while(0)

int main(){
    const uint64_t S=1u<<22;
    // best input differential per hash from the fold/scan search: complement two fold-feeding words.
    printf("=== Model: RANDOM secret/seed; attacker chooses the message pair; P is over the secret ===\n\n");

    printf("MUM v3 -- complement two ADJACENT interior words (w1,w2) of a 32B message (key-free):\n");
    { M a=rnd(32,7); M b=a; b.setw(1,~a.w(1)); b.setw(2,~a.w(2));
      SHOW("MUM v3 (unroll 8)",Mum<8>,a,b,S);
      SHOW("MUM v3 (unroll 16)",Mum<16>,a,b,S); }

    printf("\nwyhash / rapidhash (RANDOM secret) -- complement w0,w1 (first _wymix operands):\n");
    { M a=rnd(32,1); M b=a; b.setw(0,~a.w(0)); b.setw(1,~a.w(1));
      SHOW("wyhash 4.3 (random secret)",Wyhash<true>,a,b,S);
      SHOW("rapidhash v1 (random secret)",Rapidhash<true>,a,b,S); }

    printf("\nXXH3-64 (RANDOM seed) -- complement w0,w1 (first mix16B operands):\n");
    { M a=rnd(32,11); M b=a; b.setw(0,~a.w(0)); b.setw(1,~a.w(1));
      SHOW("XXH3-64 (random seed)",Xxh3<true>,a,b,S); }

    printf("\nProven hashes on the SAME MUM key-free pair (must stay ~2^-64):\n");
    { M a=rnd(32,7); M b=a; b.setw(1,~a.w(1)); b.setw(2,~a.w(2));
      SHOW("Paper GF(2^64) [proven]",PaperGF64,a,b,S);
      SHOW("Paper Mersenne [proven]",PaperMersenne,a,b,S);
      SHOW("Vector multiply-shift [proven]",VectorMultShift,a,b,S); }
    return 0;
}

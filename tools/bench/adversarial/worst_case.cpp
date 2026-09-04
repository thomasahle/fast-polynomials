// Emit explicit worst-case colliding message pairs for fast SMHasher hashes, and verify.
#include "hashes.h"
#include <cstdio>
#include <cstring>
static void hex(const char* tag, const uint8_t* b, size_t len){
    printf("  %s: ", tag); for(size_t i=0;i<len;i++) printf("%02x", b[i]); printf("\n");
}
template<class H> static uint64_t rate(const uint8_t* m1,size_t l1,const uint8_t* m2,size_t l2,uint64_t seeds){
    uint64_t c=0; Rng r(999);
    for(uint64_t i=0;i<seeds;i++){ H h; h.seed(r); if(h(m1,l1)==h(m2,l2)) c++; }
    return c;
}
struct M { uint8_t b[256]; size_t len; uint64_t w(int i)const{uint64_t v;memcpy(&v,b+8*i,8);return v;} void setw(int i,uint64_t v){memcpy(b+8*i,&v,8);} };
static M rnd(size_t len,uint64_t salt){ M m; m.len=len; Rng r(salt); for(size_t i=0;i<len;i+=8){uint64_t v=r.next();memcpy(m.b+i,&v,8);} return m; }
#define SHOW(name,H,m1,m2,S) do{ uint64_t c=rate<H>(m1.b,m1.len,m2.b,m2.len,S); \
    printf("    %-34s : %llu / %llu%s\n", name, (unsigned long long)c,(unsigned long long)S, c==S?"   (EVERY seed)":(c==0?"   (never)":"")); }while(0)

int main(){
    const uint64_t S=1u<<16;
    const uint64_t WSEC1=0x8bb84b93962eacc9ull;    // wyhash/rapidhash default secret[1]
    const uint64_t KSEC0=0xbe4ba423396cfeb8ull;    // XXH3 kSecret[0..8]

    printf("=== wyhash / rapidhash: word at offset len-16 (=word 2 of a 32B msg) set to the PUBLIC secret[1] ===\n");
    printf("    (a ^= secret[1] becomes 0, annihilating the final multiply -> output independent of the rest)\n");
    { M a=rnd(32,1), b=rnd(32,2); a.setw(2,WSEC1); b.setw(2,WSEC1);   // two unrelated msgs, word2 pinned
      hex("msg A",a.b,32); hex("msg B",b.b,32);
      SHOW("wyhash 4.3 (default secret)",Wyhash<false>,a,b,S);
      SHOW("wyhash 4.3 (RANDOM secret)",Wyhash<true>,a,b,S);
      SHOW("rapidhash v1 (default secret)",Rapidhash<false>,a,b,S);
      SHOW("Paper GF(2^64) [proven]",PaperGF64,a,b,S);
      SHOW("Vector multiply-shift [proven]",VectorMultShift,a,b,S); }

    printf("\n=== MUM v3: two 32B messages differing by all-ones XOR in two adjacent words (key-free) ===\n");
    { M a=rnd(32,7); M b=a; b.setw(1,~a.w(1)); b.setw(2,~a.w(2));
      hex("msg A",a.b,32); hex("msg B",b.b,32);
      SHOW("MUM v3 (unroll 8)",Mum<8>,a,b,S);
      SHOW("MUM v3 (unroll 16)",Mum<16>,a,b,S);
      SHOW("Paper Mersenne [proven]",PaperMersenne,a,b,S); }

    printf("\n=== XXH3-64 (seed 0): w0 = kSecret[0..8] zeroes mix16B(chunk 0); vary w1 ===\n");
    { M a=rnd(32,11); M b=a; a.setw(0,KSEC0); b.setw(0,KSEC0); b.setw(1,~a.w(1));
      hex("msg A",a.b,32); hex("msg B",b.b,32);
      SHOW("XXH3-64 (seed 0)",Xxh3<false>,a,b,S);
      SHOW("XXH3-64 (random seed)",Xxh3<true>,a,b,S);
      SHOW("Paper GF(2^64) [proven]",PaperGF64,a,b,S); }
    return 0;
}

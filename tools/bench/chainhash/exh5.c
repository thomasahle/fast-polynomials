/* exh5.c -- exhaustive sanity check of the explicit degree-5 decoder
 * (eq:ph:chain5-decoder) over GF(2), GF(4), GF(8), GF(16), GF(32).
 * Companion of exh7.c (the former degree-7 chain).  The decoder IS the proof; this only
 * guards against transcription errors (AGENTS.md rule 1).
 *
 * Circuit (CIRCUITS[5] of website/js/char2.js):
 *     y = x x;  z = (y + c0)(x + y + c1);  t = (x + c2)(z + c3);  f = t + c4
 * Rows x^4..x^0 in the pivot coordinates q = (c2, c0+c1, c0, c3, c4):
 *     e4 = q0 + 1
 *     e3 = q1 + q0
 *     e2 = q2 + q0 q1
 *     e1 = q3 + delta + q0 q2         delta = q2 (q1 + q2) = c0 c1
 *     e0 = q4 + q0 (delta + q3)
 * All pivots are the identity: no Frobenius root, valid over every field of
 * characteristic 2.  Inverse coordinates: c = (q2, q1+q2, q0, q3, q4).
 *
 * Build/run:  cc -O2 -o exh5 exh5.c && ./exh5
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K, Q; static unsigned mod; static unsigned mul[32][32];
static unsigned gmul(unsigned a, unsigned b){unsigned r=0;for(int i=0;i<K;i++){if(b>>i&1)r^=a<<i;} for(int i=2*K-2;i>=K;i--) if(r>>i&1) r^=mod<<(i-K); return r;}
static void enc(const unsigned*c, unsigned*g){ /* g[i] = coeff of X^i, i=0..4, from eq:ph:chain5-coeffs */
  unsigned b=c[0]^c[1], d=mul[c[0]][c[1]];
  g[4]=1^c[2]; g[3]=b^c[2]; g[2]=c[0]^mul[c[2]][b]; g[1]=d^c[3]^mul[c[0]][c[2]]; g[0]=c[4]^mul[c[2]][d^c[3]];
}
static unsigned evalcirc(const unsigned*c, unsigned x){ /* the circuit itself, gate by gate */
  unsigned y=mul[x][x], z=mul[y^c[0]][x^y^c[1]], t=mul[x^c[2]][z^c[3]]; return t^c[4];
}
static unsigned evalpoly(const unsigned*g, unsigned x){ /* Horner on the monic quintic */
  unsigned acc=1; for(int i=4;i>=0;i--) acc=mul[acc][x]^g[i]; return acc;
}
static void dec(const unsigned*g, unsigned*c){
  unsigned q0=g[4]^1; unsigned q1=g[3]^q0; unsigned q2=g[2]^mul[q0][q1];
  unsigned d=mul[q2][q1^q2];
  unsigned q3=g[1]^d^mul[q0][q2];
  unsigned q4=g[0]^mul[q0][d^q3];
  c[0]=q2; c[1]=q1^q2; c[2]=q0; c[3]=q3; c[4]=q4;
}
int main(){ unsigned mods[6]={0,3,7,11,19,37}; /* x+1, x^2+x+1, x^3+x+1, x^4+x+1, x^5+x^2+1 */
 for(K=1;K<=5;K++){ mod=mods[K]; Q=1<<K; for(int a=0;a<Q;a++)for(int b=0;b<Q;b++)mul[a][b]=gmul(a,b);
  uint64_t N=1; for(int i=0;i<5;i++)N*=Q; uint8_t*seen=calloc(N/8+1,1); uint64_t bad=0,dup=0,mism=0;
  for(uint64_t idx=0;idx<N;idx++){ unsigned c[5],g[5],c2[5]; uint64_t t=idx; for(int i=0;i<5;i++){c[i]=t%Q;t/=Q;}
   enc(c,g); dec(g,c2); if(memcmp(c,c2,sizeof c)) bad++; uint64_t gi=0; for(int i=4;i>=0;i--) gi=gi*Q+g[i];
   if(seen[gi>>3]>>(gi&7)&1) dup++; seen[gi>>3]|=1<<(gi&7);
   for(unsigned x=0;x<(unsigned)Q;x++) if(evalcirc(c,x)!=evalpoly(g,x)) mism++; }
  printf("GF(%d): %llu vectors, decode failures %llu, duplicate images %llu, circuit/table evaluation mismatches %llu\n",Q,(unsigned long long)N,(unsigned long long)bad,(unsigned long long)dup,(unsigned long long)mism); free(seen);}
 return 0;}

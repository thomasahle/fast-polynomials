#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K, Q; static unsigned mod; static unsigned mul[16][16]; static unsigned sq[16], sqrtt[16];
static unsigned gmul(unsigned a, unsigned b){unsigned r=0;for(int i=0;i<K;i++){if(b>>i&1)r^=a<<i;} for(int i=2*K-2;i>=K;i--) if(r>>i&1) r^=mod<<(i-K); return r;}
static void enc(const unsigned*c, unsigned*g){ /* g[i] = coeff of X^i, i=0..6 */
  unsigned b=c[0]^c[1], e=c[2]^mul[c[0]][c[1]], d=mul[c[1]][c[2]];
  unsigned A=sq[b], Bc=mul[c[3]][b], E2=sq[e], D2=sq[d];
  g[6]=c[4]; g[5]=A; g[4]=c[3]^mul[c[4]][A]; g[3]=E2^Bc^1^mul[c[3]][c[4]];
  unsigned r2=mul[c[3]][e]^c[0], r1=D2^mul[c[3]][d]^c[5];
  g[2]=r2^mul[c[4]][E2^Bc^1]; g[1]=r1^mul[c[4]][r2]; g[0]=c[6]^mul[c[4]][r1];
}
static void dec(const unsigned*g, unsigned*c){
  unsigned q0=g[6]; unsigned q1=sqrtt[g[5]]; unsigned q2=g[4]^mul[q0][sq[q1]];
  unsigned q3=sqrtt[g[3]^mul[q2][q1]^1^mul[q2][q0]];
  unsigned q4=g[2]^mul[q2][q3]^q1^mul[q0][sq[q3]^mul[q2][q1]^1];
  unsigned d=mul[q4][q3^mul[q1][q4]^sq[q4]];
  unsigned q5=g[1]^sq[d]^mul[q2][d]^mul[q0][mul[q2][q3]^q1^q4];
  unsigned q6=g[0]^mul[q0][sq[d]^mul[q2][d]^q5];
  c[0]=q1^q4; c[1]=q4; c[2]=q3^mul[q1][q4]^sq[q4]; c[3]=q2; c[4]=q0; c[5]=q5; c[6]=q6;
}
int main(){ unsigned mods[5]={0,3,7,11,19};
 for(K=1;K<=4;K++){ mod=mods[K]; Q=1<<K; for(int a=0;a<Q;a++)for(int b=0;b<Q;b++)mul[a][b]=gmul(a,b);
  for(int a=0;a<Q;a++){sq[a]=mul[a][a];} for(int a=0;a<Q;a++)sqrtt[sq[a]]=a;
  uint64_t N=1; for(int i=0;i<7;i++)N*=Q; uint8_t*seen=calloc(N/8+1,1); uint64_t bad=0,dup=0;
  for(uint64_t idx=0;idx<N;idx++){ unsigned c[7],g[7],c2[7]; uint64_t t=idx; for(int i=0;i<7;i++){c[i]=t%Q;t/=Q;}
   enc(c,g); dec(g,c2); if(memcmp(c,c2,sizeof c)) bad++; uint64_t gi=0; for(int i=6;i>=0;i--) gi=gi*Q+g[i];
   if(seen[gi>>3]>>(gi&7)&1) dup++; seen[gi>>3]|=1<<(gi&7);}
  printf("GF(%d): %llu vectors, decode failures %llu, duplicate images %llu\n",Q,(unsigned long long)N,(unsigned long long)bad,(unsigned long long)dup); free(seen);}
 return 0;}

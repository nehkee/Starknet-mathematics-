/* Independent exhaustive check of Lemma CG (rukafe0x, result 27, row M-1002).
 * For e = 2h + c, 1 <= c <= h-1: no h-subset S of mu_e has A_S^3 (A_S = prod_{s in S}(X - s))
 * with zero coefficients in degrees h+c+1 .. e-1 (equivalently, after S -> S^-1, F_S^3 zero in
 * degrees h-c+1 .. 2h-c-1).  Both windows are tested independently on every subset.
 * Field: F_p (p prime, e | p-1), or F_{p^2} = F_p[i]/(i^2+1) for p = 3 mod 4 with e | p^2-1.
 * Usage: cg_search P EXT E H [C]   (EXT = 1 for F_p, 2 for F_{p^2}); C defaults to E - 2H. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static uint64_t P; static int EXT;
typedef struct { uint64_t a, b; } fe;   /* a + b i (b = 0 when EXT = 1) */
static inline uint64_t md(u128 x){ return (uint64_t)(x % P); }
static inline fe add(fe x, fe y){ fe r={ (x.a+y.a)%P, (x.b+y.b)%P }; return r; }
static inline fe sub(fe x, fe y){ fe r={ (x.a+P-y.a)%P, (x.b+P-y.b)%P }; return r; }
static inline fe mul(fe x, fe y){
  if (EXT==1){ fe r={ md((u128)x.a*y.a), 0 }; return r; }
  /* (a+bi)(c+di) = ac - bd + (ad + bc) i */
  fe r={ (md((u128)x.a*y.a) + P - md((u128)x.b*y.b)) % P, md((u128)x.a*y.b + (u128)x.b*y.a) };
  return r; }
static inline int iszero(fe x){ return x.a==0 && x.b==0; }
static fe fpow(fe x, u128 n){ fe r={1,0}; while(n){ if(n&1) r=mul(r,x); x=mul(x,x); n>>=1;} return r; }
static int E,H,C; static fe roots[128]; static fe poly[64][64]; /* poly[d] = product of first d chosen roots */
static long long leaves=0, hitsA=0, hitsF=0; static int chosen[64];
static void check(void){
  fe *A = poly[H]; /* monic degree H: A[0..H] */
  fe A2[200]={0}, A3[200]={0};
  for(int i=0;i<=2*H;i++){A2[i].a=A2[i].b=0;}
  for(int i=0;i<=H;i++) for(int j=0;j<=H;j++) A2[i+j]=add(A2[i+j],mul(A[i],A[j]));
  for(int i=0;i<=3*H;i++){A3[i].a=A3[i].b=0;}
  for(int i=0;i<=2*H;i++) for(int j=0;j<=H;j++) A3[i+j]=add(A3[i+j],mul(A2[i],A[j]));
  int okA=1; for(int d=H+C+1; d<=E-1; d++) if(!iszero(A3[d])){okA=0;break;}
  int okF=1; for(int d=H-C+1; d<=2*H-C-1; d++) if(!iszero(A3[d])){okF=0;break;}
  leaves++; if(okA){hitsA++; if(hitsA<=3){printf("  HIT(A-window) S =");for(int i=0;i<H;i++)printf(" %d",chosen[i]);printf("\n");}}
  if(okF){hitsF++; if(hitsF<=3){printf("  HIT(F-window) S =");for(int i=0;i<H;i++)printf(" %d",chosen[i]);printf("\n");}}
}
static void rec(int start, int d){
  if(d==H){ check(); return; }
  for(int s=start; s<=E-(H-d); s++){
    chosen[d]=s; fe *o=poly[d], *nw=poly[d+1]; fe r=roots[s];
    /* nw = o * (X - r) */
    for(int i=0;i<=d+1;i++){ fe t={0,0}; if(i>=1) t=o[i-1]; if(i<=d) t=sub(t,mul(o[i],r)); nw[i]=t; }
    rec(s+1,d+1);
  }
}
int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage\n");return 2;}
  P=strtoull(argv[1],0,10); EXT=atoi(argv[2]); E=atoi(argv[3]); H=atoi(argv[4]); C = argc>5? atoi(argv[5]) : E-2*H;
  u128 order = EXT==1 ? (u128)(P-1) : (u128)P*P-1;
  if(order % E){ fprintf(stderr,"e does not divide group order\n"); return 2; }
  /* find an element of exact order E */
  fe w={0,0}; uint64_t seed=3;
  for(;;seed++){
    fe g={seed%P, EXT==2? (seed*7+1)%P:0}; w=fpow(g, order/E);
    int ok=1; fe t={1,0};
    for(int i=1;i<E;i++){ t=mul(t,w); if(t.a==1&&t.b==0){ok=0;break;} }
    t=mul(t,w); if(ok && t.a==1 && t.b==0) break;
  }
  fe t={1,0}; for(int i=0;i<E;i++){ roots[i]=t; t=mul(t,w); }
  poly[0][0].a=1; poly[0][0].b=0;
  rec(0,0);
  printf("p=%llu ext=%d e=%d h=%d c=%d threshold(4h+c-2)=%d subsets=%lld hitsA=%lld hitsF=%lld\n",
    (unsigned long long)P,EXT,E,H,C,4*H+C-2,leaves,hitsA,hitsF);
  return 0;
}

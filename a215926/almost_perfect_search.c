// search almost perfect numbers k = 2^a * m^2 (m odd >=3), k <= L=M^2, sigma(k) = 2k-1
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  uint64_t M = strtoull(argv[1],0,10);
  uint32_t *spf = malloc((M+1)*sizeof(uint32_t));
  for(uint64_t i=0;i<=M;i++) spf[i]=0;
  for(uint64_t i=2;i<=M;i++) if(!spf[i]) for(uint64_t j=i;j<=M;j+=i) if(!spf[j]) spf[j]=i;
  u128 L = (u128)M*M; long found=0; unsigned long long tested=0;
  for(uint64_t m=3;m<=M;m+=2){
    u128 sig=1; uint64_t x=m;
    while(x>1){ uint64_t p=spf[x]; int e=0; while(x%p==0){x/=p;e++;}
      u128 t=1,pw=1; for(int i=0;i<2*e;i++){pw*=p;t+=pw;} sig*=t; }
    u128 m2=(u128)m*m; 
    for(int a=0;;a++){ u128 k=m2<<a; if(k>L) break; tested++;
      u128 P=((u128)1<<(a+1));
      if((P-1)*sig+1==P*m2){ found++; printf("FOUND a=%d m=%llu\n",a,(unsigned long long)m);} }
  }
  printf("M=%llu L=M^2 tested=%llu found=%ld\n",(unsigned long long)M,tested,found);
}

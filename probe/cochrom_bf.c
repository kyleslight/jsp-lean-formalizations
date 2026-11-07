#include <stdio.h>
#include <stdlib.h>
static int n, N;
static unsigned char adjmask[9];
static unsigned char cl[512], ind[512], dp[512];
int main(int argc, char** argv){
  int nlo=atoi(argv[1]), nhi=atoi(argv[2]);
  for (n=nlo;n<=nhi;n++){
    N=1<<n; int P=n*(n-1)/2; unsigned long long tot=1ULL<<P;
    int best=0; unsigned long long bestg=0;
    for (unsigned long long g=0; g<tot; g++){
      for(int v=0;v<n;v++) adjmask[v]=0;
      int k=0;
      for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ if((g>>k)&1ULL){adjmask[i]|=1<<j; adjmask[j]|=1<<i;} k++; }
      cl[0]=ind[0]=1;
      for(int s=1;s<N;s++){ int v=__builtin_ctz(s); int r=s^(1<<v);
        cl[s]= cl[r] && ((r==0)||((adjmask[v]&r)==r));
        ind[s]= ind[r] && ((adjmask[v]&r)==0); }
      dp[0]=0;
      for(int s=1;s<N;s++){ int low=s&(-s); int rest=s^low; int bv=100; int sub=rest;
        while(1){ int T=sub|low; if(cl[T]||ind[T]){int c=1+dp[s^T]; if(c<bv)bv=c;} if(sub==0)break; sub=(sub-1)&rest; }
        dp[s]=bv; }
      int z=dp[N-1];
      if(z>best){best=z;bestg=g;}
    }
    printf("n=%d f(n)=%d witness=%llu\n",n,best,bestg); fflush(stdout);
  }
}

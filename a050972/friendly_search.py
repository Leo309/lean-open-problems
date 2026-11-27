# Search for friendly pairs a < b <= B (same sigma(n)/n) with a practical and b not practical.
# Usage: python3 friendly_search.py 30000000
# Prints the number of such pairs and the first ones as (b, a, numerator, denominator).
import numpy as np, sys
B=int(sys.argv[1])
sig=np.zeros(B+1,dtype=np.int64)
for d in range(1,B+1):
    sig[d::d]+=d
n=np.arange(B+1,dtype=np.int64)
g=np.gcd(sig,n); g[0]=1
num=sig//g; den=n//g
idx=np.lexsort((n[1:],den[1:],num[1:]))+1
# smallest prime factor sieve for practical test
def practical(m):
    if m==1: return True
    if m%2: return False
    s=1; x=m; p=2
    while p*p<=x:
        if x%p==0:
            if p>1+s: return False
            e=1
            pk=1; t=1
            while x%p==0: x//=p; pk*=p; t+=pk
            s*=t
        p+=1
    if x>1:
        if x>1+s: return False
    return True
out=[]
i=0; L=len(idx)
ks_num=num[idx]; ks_den=den[idx]
start=0
for j in range(1,L+1):
    if j==L or ks_num[j]!=ks_num[start] or ks_den[j]!=ks_den[start]:
        if j-start>=2:
            grp=[int(x) for x in idx[start:j]]
            pr=[practical(x) for x in grp]
            # counterexample: a<b, a practical, b not
            firstp=next((x for x,q in zip(grp,pr) if q),None)
            if firstp is not None:
                for x,q in zip(grp,pr):
                    if x>firstp and not q: out.append((x,firstp,int(ks_num[start]),int(ks_den[start])))
        start=j
out.sort()
print(len(out)); print(out[:30])

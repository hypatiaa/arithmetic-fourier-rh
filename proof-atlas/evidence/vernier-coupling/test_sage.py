"""Run with the Sage environment's Python beside sweep.pyx to produce geometry.json."""
from itertools import combinations
from math import isqrt
from pathlib import Path
import json
import sys

import pyximport
from sage.all import ZZ, QQ, binomial, matrix, moebius
from sage.version import version

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
pyximport.install(language_level=3)
from sweep import signs, counts, matched, interval_deficit

CUTOFFS = [5, 9, 40, 720, 1000, 10000, 100000, 1000000, 10000000,
           30922618, 49098878, 73791943, 100000000]
SCAN_END = 20000

def entry(i, j, h):
    k = h + j - i
    return binomial(2*h, k) if 0 <= k <= 2*h else ZZ.zero()

def oracle_check(mu):
    # Direct arithmetic and ranks never call the pairing algorithm.
    for q in range(1, 20000, 2):
        assert mu[q//2] == (0 if q % 3 == 0 else moebius(q))
    checked = 0
    for x in list(range(2, 121)) + [160, 201, 355, 500, 720]:
        for twist in [False, True]:
            band=[q for q in range(x//2+1,x+1) if q%2 and q%3 and moebius(q)]
            def sign(q):
                return moebius(q) * (-1 if twist and q%4==3 else 1)
            pos=[q//2 for q in band if sign(q)==1]
            neg=[q//2 for q in band if sign(q)==-1]
            assert counts(mu,x,twist)==(len(pos),len(neg))
            for h in sorted({0,1,2,isqrt(x),x}):
                mat=matrix(QQ,len(pos),len(neg),lambda i,j:entry(pos[i],neg[j],h))
                assert mat.rank()==matched(mu,x,twist,h)
                checked+=1
    # Every 1-, 2-, and 3-point minor on a small integer grid.
    minors=0
    for h in (1,2,3):
        for size in (1,2,3):
            for rows in combinations(range(6),size):
                for cols in combinations(range(6),size):
                    det=matrix(ZZ,size,size,lambda i,j:entry(rows[i],cols[j],h)).det()
                    assert det>=0 and bool(det)==all(abs(i-j)<=h for i,j in zip(rows,cols))
                    minors+=1
    return {"rank_tests":checked,"minor_tests":minors,"mobius_checks":10000}

def scan(mu):
    out=[]
    for twist in (False,True):
        first_excess=None
        first_above_sqrt=None
        defects=0
        best_x,best_u=2,0
        max_extra=(0,2)
        for x in range(2,SCAN_END+1):
            p,n=counts(mu,x,twist)
            unmatched=p+n-2*matched(mu,x,twist,isqrt(x))
            extra=unmatched-abs(p-n)
            assert extra>=0 and extra%2==0
            if extra:
                defects+=1
                if first_excess is None:
                    first_excess=[x,unmatched,p-n]
            if unmatched**2>x and first_above_sqrt is None:
                first_above_sqrt=[x,unmatched,p-n]
            if unmatched**2*best_x>best_u**2*x:
                best_x,best_u=x,unmatched
            if extra>max_extra[0]:
                max_extra=(extra,x)
        out.append(dict(twist=twist,through=SCAN_END,cutoffs_with_extra=defects,
                        first_excess=first_excess,first_above_sqrt=first_above_sqrt,
                        peak=[best_x,best_u],largest_extra_then_cutoff=max_extra))
    return out

def main():
    mu=signs(max(CUTOFFS))
    checks=oracle_check(mu)
    result=dict(sage=version,checks=checks,all_cutoffs=scan(mu),samples=[],certificates=[])
    for x in CUTOFFS:
        refcounts=None
        for twist in (False,True):
            p,n=counts(mu,x,twist)
            if refcounts is None:
                refcounts=p+n
            assert p+n==refcounts
            h=isqrt(x)
            local=matched(mu,x,twist,h)
            near=matched(mu,x,twist,1)
            assert local>=near and local<=min(p,n)
            shared=matched(mu,x,twist,h,0)+matched(mu,x,twist,h,1)
            # Same pair set works for both characters when matched by mod-4 class.
            if twist:
                assert shared==result["samples"][-1]["shared_pairs"]
            sample=dict(x=x,twist=twist,p=p,n=n,v=p-n,det1_unmatched=p+n-2*near,
                        radius=h,local_unmatched=p+n-2*local,extra=p+n-2*local-abs(p-n),
                        shared_pairs=shared,shared_unmatched=p+n-2*shared)
            result["samples"].append(sample)
        print(x,[(r["v"],r["local_unmatched"],r["shared_unmatched"]) for r in result["samples"][-2:]],flush=True)
    for x,twist in [(115,True),(1417,False),(1000000,True),(100000000,True)]:
        p,n=counts(mu,x,twist)
        h=isqrt(x)
        m=matched(mu,x,twist,h)
        minority=1 if p<=n else -1
        witness=interval_deficit(mu,x,twist,h,minority)
        deficit,l,r,cm,ca=witness
        assert 0<=deficit<=min(p,n)-m and cm-ca==deficit
        if x<=1000000 and deficit:
            def sign(q):
                return mu[q//2]*(-1 if twist and q%4==3 else 1)
            assert cm==sum(sign(q)==minority for q in range(l,r+1,2))
            first=max(2*((x//2+1)//2)+1,l-2*h)
            assert ca==sum(sign(q)==-minority for q in range(first,min(x,r+2*h)+1,2))
        low,high=h,x
        while low<high:
            middle=(low+high)//2
            if matched(mu,x,twist,middle)==min(p,n):
                high=middle
            else:
                low=middle+1
        assert matched(mu,x,twist,low)==min(p,n) and matched(mu,x,twist,low-1)<min(p,n)
        result["certificates"].append(dict(x=x,twist=twist,minority=minority,
            unmatched_minority=min(p,n)-m,interval=witness,min_saturating_radius=low))
    (HERE/"geometry.json").write_text(json.dumps(result,indent=2)+"\n")
    print(checks,result["all_cutoffs"],flush=True)

if __name__=="__main__":
    main()

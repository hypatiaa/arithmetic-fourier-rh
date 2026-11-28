"""Certify the square-root comparison for every integer cutoff in a finite range."""
import json
from heapq import heappush, heappop
from math import isqrt
from pathlib import Path
import pyximport
from sage.version import version
from sage.all import QQ

pyximport.install(language_level=3)
from sweep import signs, cover, counts, matched

END=100_000_000
mu=signs(END)
output={"sage":version,"through":END,"grades":[]}
for twist in (False,True):
    records=[]
    # Test the range-add certificate against direct matches on small slabs.
    for a in range(2,500,11):
        b=a+9
        u,x,_,_=cover(mu,a,b,twist,isqrt(a))
        for t in range(a,b+1):
            exact=sum(counts(mu,t,twist))-2*matched(mu,t,twist,isqrt(t))
            assert QQ(exact*exact)/t <= QQ(u*u)/x
            assert cover(mu,t,t,twist,isqrt(t))[:2]==(exact,t)
    def certify(a,b,depth=0):
        u,x,over,first=cover(mu,a,b,twist,isqrt(a))
        if over and a<b and depth<4:
            mid=(a+b)//2
            certify(a,mid,depth+1)
            certify(mid+1,b,depth+1)
        else:
            records.append([a,b,u,x,over,first])
    a=2
    while a<=END:
        b=min(END,max(a+15,a+a//4))
        certify(a,b)
        a=b+1
    assert records[0][0]==2 and records[-1][1]==END
    assert all(s[1]+1==t[0] for s,t in zip(records,records[1:]))
    worst=max(records,key=lambda row: QQ(row[2]*row[2])/row[3])
    unresolved=[r for r in records if r[4]]
    probes=[]
    for a,b,u,x,over,first in unresolved:
        for t in sorted({x,first}):
            value=sum(counts(mu,t,twist))-2*matched(mu,t,twist,isqrt(t))
            probes.append([t,value])
    output["grades"].append(dict(twist=twist,slabs=records,worst=worst,
        uncertified_at_constant_one=sum(r[4] for r in unresolved),direct_probes=probes))
    print("twist",twist,"slabs",len(records),"worst",worst,"slabs above one",len(unresolved),flush=True)
    # Bound-and-split only the ranges whose explicit matching could exceed
    # the largest exact ratio already attained by the optimal matching.
    queue=[]
    leaves=[]
    peak_x,peak_u=2,0
    def enqueue(rec):
        a,b,u,x,_,_=rec
        heappush(queue,(-QQ(u*u)/x,a,b,rec))
    for rec in records:
        enqueue(rec)
    refinements=0
    while queue:
        neg_bound,a,b,rec=heappop(queue)
        if -neg_bound<=QQ(peak_u*peak_u)/peak_x:
            leaves.append(rec)
            continue
        t=rec[3]
        actual=sum(counts(mu,t,twist))-2*matched(mu,t,twist,isqrt(t))
        assert actual<=rec[2]
        if QQ(actual*actual)/t>QQ(peak_u*peak_u)/peak_x:
            peak_x,peak_u=t,actual
        if -neg_bound<=QQ(peak_u*peak_u)/peak_x:
            leaves.append(rec)
        elif refinements<500 and a<b:
            mid=(a+b)//2
            for lo,hi in [(a,mid),(mid+1,b)]:
                enqueue([lo,hi,*cover(mu,lo,hi,twist,isqrt(lo))])
            refinements+=1
        else:
            leaves.append(rec)
    leaves.sort()
    assert leaves[0][0]==2 and leaves[-1][1]==END
    assert all(s[1]+1==t[0] for s,t in zip(leaves,leaves[1:]))
    best_upper=max(QQ(r[2]*r[2])/r[3] for r in leaves)
    output["grades"][-1].update(refined_slabs=leaves,exact_witness=[peak_x,peak_u],
        peak_certified=(best_upper==QQ(peak_u*peak_u)/peak_x),squared_peak_upper=str(best_upper))
    print("refinements",refinements,"witness",peak_x,peak_u,"upper ratio squared",best_upper,flush=True)
Path(__file__).with_name("coverage.json").write_text(json.dumps(output,indent=1)+"\n")

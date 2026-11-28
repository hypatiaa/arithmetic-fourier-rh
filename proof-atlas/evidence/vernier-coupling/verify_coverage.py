"""Check all upper certificates and the two attaining lower witnesses with separate code."""
from math import isqrt
from pathlib import Path
import json
import numpy as np
import pyximport
from sage.all import moebius, QQ
from sage.version import version

pyximport.install(language_level=3)
from recheck import independent_mu, verify_slab

here=Path(__file__).resolve().parent
data=json.loads((here/"coverage.json").read_text())
limit=data["through"]
assert limit==100_000_000
mu=independent_mu(limit)
prefix=np.empty(len(mu)+1,dtype=np.int32)
prefix[0]=0
np.cumsum(np.asarray(mu)!=0,dtype=np.int32,out=prefix[1:])
results=[]
for grade in data["grades"]:
    twist=grade["twist"]
    x,u=grade["exact_witness"]
    assert (x,u)==((85,6) if twist else (73,8))
    assert grade["peak_certified"] and QQ(grade["squared_peak_upper"])==QQ(u*u)/x
    signed=sum(moebius(q)*(-1 if twist and q%4==3 else 1)
               for q in range(x//2+1,x+1) if q%2 and q%3)
    assert abs(signed)==u
    next_x=2
    for a,b,*_ in grade["refined_slabs"]:
        assert a==next_x and a<=b
        verify_slab(mu,prefix,a,b,twist,isqrt(a),x,u)
        next_x=b+1
    assert next_x==limit+1
    results.append(dict(twist=twist,checked_cutoffs=limit-1,slabs=len(grade["refined_slabs"]),
                        argmax_witness=x,signed=int(signed),squared_peak=grade["squared_peak_upper"]))
    print(results[-1],flush=True)
(here/"independent.json").write_text(json.dumps(dict(sage=version,results=results),indent=2)+"\n")

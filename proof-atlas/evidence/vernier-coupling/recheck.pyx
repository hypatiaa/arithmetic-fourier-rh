# cython: language_level=3, boundscheck=False, wraparound=False, cdivision=True
from array import array

def independent_mu(int last):
    """Euler's odd linear sieve; each odd composite is written once."""
    cdef int size=(last+1)//2, q,p,k,t,each
    cdef long long product
    raw=array('b',[0])*size
    cdef signed char[::1] m=raw
    cdef int[::1] least=array('i',[0])*size
    primes=array('i')
    m[0]=1
    for k in range(1,size):
        q=2*k+1
        if least[k]==0:
            least[k]=q
            primes.append(q)
            m[k]=-1
        for t in range(len(primes)):
            p=primes[t]
            product=<long long>p*q
            if product>last or p>least[k]:
                break
            each=<int>(product//2)
            least[each]=p
            m[each]=0 if p==least[k] else -m[k]
    for k in range(1,size,3):
        m[k]=0
    return raw

def verify_slab(signed char[::1] mu, int[::1] prefix, int a, int b, bint twist,
                int h, int top_x, int top_u):
    """FIFO matching on the superband; independent prefix counts for each subband."""
    cdef int[::1] diff=array('i',[0])*(b-a+2)
    cdef int capacity=h+2
    cdef int[::1] queue=array('i',[0])*capacity
    cdef int head=0,length=0,grade=0,s,i,lo_q,hi_q,first,last,x,n=0,u,qcount
    for i in range((a//2+1)//2,(b+1)//2):
        while length and i-queue[head]>h:
            head=(head+1)%capacity
            length-=1
        s=mu[i]
        if twist and i%2:
            s=-s
        if s==0:
            continue
        if length and s!=grade:
            lo_q=2*queue[head]+1
            hi_q=2*i+1
            assert (hi_q-lo_q)//2<=h
            head=(head+1)%capacity
            length-=1
            first=max(a,hi_q)
            last=min(b,2*lo_q-1)
            if first<=last:
                diff[first-a]+=1
                diff[last+1-a]-=1
        else:
            assert length<capacity
            grade=s
            queue[(head+length)%capacity]=i
            length+=1
    for x in range(a,b+1):
        n+=diff[x-a]
        qcount=prefix[(x+1)//2]-prefix[(x//2+1)//2]
        u=qcount-2*n
        assert 0<=u<=qcount
        assert (<long long>u*u)*top_x <= (<long long>top_u*top_u)*x

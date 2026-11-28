# cython: language_level=3, boundscheck=False, wraparound=False, cdivision=True
"""Exact integer loops used by the Sage driver. Index i denotes q=2i+1."""
from array import array

def signs(int limit):
    cdef int size = (limit+1)//2
    raw = array('b', [1]) * size
    cdef signed char[::1] mu = raw
    cdef unsigned char[::1] composite = bytearray(size)
    cdef int p, i
    cdef long long square
    for p in range(3, limit+1, 2):
        if composite[p//2]:
            continue
        square = <long long>p*p
        if square <= limit:
            for i in range(<int>(square//2), size, p):
                composite[i] = 1
        for i in range(p//2, size, p):
            if p == 3:
                mu[i] = 0
            else:
                mu[i] = -mu[i]
        if square <= limit:
            for i in range(<int>(square//2), size, <int>square):
                mu[i] = 0
    return raw

cdef inline int grade(signed char[::1] mu, int index, bint twist, int residue) noexcept:
    if residue >= 0 and index % 2 != residue:
        return 0
    if twist and index % 2:
        return -mu[index]
    return mu[index]

def counts(signed char[::1] mu, int x, bint twist):
    cdef int i, s, p=0, n=0
    for i in range((x//2+1)//2, (x+1)//2):
        s = grade(mu,i,twist,-1)
        p += s > 0
        n += s < 0
    return p,n

def matched(signed char[::1] mu, int x, bint twist, int radius, int residue=-1):
    cdef int left=(x//2+1)//2, right=(x+1)//2, i=left, j=left, pairs=0
    while i<right and j<right:
        while i<right and grade(mu,i,twist,residue)!=1:
            i+=1
        while j<right and grade(mu,j,twist,residue)!=-1:
            j+=1
        if i==right or j==right:
            break
        if i+radius < j:
            i+=1
        elif j+radius < i:
            j+=1
        else:
            pairs+=1
            i+=1
            j+=1
    return pairs

def interval_deficit(signed char[::1] mu, int x, bint twist, int h, int minority):
    """Strongest single interval witness, using all majority rows in its expanded interval."""
    cdef int low=(x//2+1)//2, high=(x+1)//2, i, k
    cdef int pre=0, before=0, after=0, minimum=0, left=low, left_m=0, left_a=0
    cdef int best=0, witness_left=0, witness_right=0, count_m=0, count_a=0
    for k in range(low,min(low+h,high)):
        after += grade(mu,k,twist,-1)==-minority
    for i in range(low,high):
        if i+h<high:
            after += grade(mu,i+h,twist,-1)==-minority
        if i-h-1>=low:
            before += grade(mu,i-h-1,twist,-1)==-minority
        if pre-before<minimum:
            minimum=pre-before
            left=i
            left_m=pre
            left_a=before
        pre += grade(mu,i,twist,-1)==minority
        if pre-after-minimum>best:
            best=pre-after-minimum
            witness_left=2*left+1
            witness_right=2*i+1
            count_m=pre-left_m
            count_a=after-left_a
    return best,witness_left,witness_right,count_m,count_a

cdef bint beats(int u,int x,int best_u,int best_x):
    if u<=250000 and best_u<=250000 and x<=100000000 and best_x<=100000000:
        return (<long long>u*u)*best_x > (<long long>best_u*best_u)*x
    return (int(u)**2)*int(best_x) > (int(best_u)**2)*int(x)

def cover(signed char[::1] mu, int a, int b, bint twist, int h):
    """A single explicit matching certifies upper bounds at every X in [a,b]."""
    changes=array('i',[0])*(b-a+2)
    cdef int[::1] delta=changes
    cdef int lo=(a//2+1)//2, hi=(b+1)//2, i=lo,j=lo,start,end,x,pairs=0
    cdef int total=sum(counts(mu,a,twist)), u, peak=0, peak_x=a, over=0, first=0
    while i<hi and j<hi:
        while i<hi and grade(mu,i,twist,-1)!=1:
            i+=1
        while j<hi and grade(mu,j,twist,-1)!=-1:
            j+=1
        if i==hi or j==hi:
            break
        if i+h<j:
            i+=1
        elif j+h<i:
            j+=1
        else:
            start=max(a,2*max(i,j)+1)
            end=min(b+1,2*(2*min(i,j)+1))
            if start<end:
                delta[start-a]+=1
                delta[end-a]-=1
            i+=1
            j+=1
    for x in range(a,b+1):
        if x>a:
            if x%2 and mu[x//2]!=0:
                total+=1
            if x%4==2 and mu[x//4]!=0:
                total-=1
        pairs+=delta[x-a]
        u=total-2*pairs
        assert u>=0
        if beats(u,x,peak,peak_x):
            peak=u
            peak_x=x
        if <long long>u*u>x:
            if over==0:
                first=x
            over+=1
    return peak,peak_x,over,first
